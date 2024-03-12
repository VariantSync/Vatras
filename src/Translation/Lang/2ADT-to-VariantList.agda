open import Framework.Definitions using (𝔽; 𝕍; 𝔸; 𝔼)
open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Relation.Binary using (DecidableEquality; Rel)
module Translation.Lang.2ADT-to-VariantList
  (F : 𝔽)
  (V : 𝕍)
  (_==_ : DecidableEquality F)
  where

open import Function using (_∘_)

open import Data.List using (List; []; _∷_)
open import Data.List.NonEmpty using (List⁺; _∷_; _⁺++⁺_; length)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _<_; _≤?_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; ≰⇒>; m≤m+n)
open import Data.Product using (_,_)

open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open Eq.≡-Reasoning

open import Data.EqIndexedSet hiding (Index; _∈_)
open Data.EqIndexedSet.≅-Reasoning

open import Framework.VariabilityLanguage
open import Framework.Relation.Expressiveness V using (_≽_; expressiveness-by-translation)
open import Framework.Properties.Soundness V using (Sound)
open import Framework.Proof.Transitive V using (soundness-by-expressiveness)
open import Lang.2ADT F V
  using (2ADT; 2ADTL; leaf; _⟨_,_⟩)
  renaming (⟦_⟧ to ⟦_⟧₂; Configuration to Conf₂)
open import Lang.VariantList V
  using (VariantList; VariantListL; VariantList-is-Sound)
  renaming (⟦_⟧ to ⟦_⟧ₗ; Configuration to Confₗ)

open import Lang.2ADT.Path F V _==_
open import Translation.Lang.2ADT.DeadElim F V _==_ as DeadElim using (node; kill-dead; ⟦_⟧ᵤ)
open import Translation.Lang.2ADT.WalkSemantics F V _==_ as Walk using ()

open import Util.List using (find-or-last; ⁺++⁺-length; ⁺++⁺-length-≤; find-or-last-append; find-or-last-prepend-+; find-or-last-prepend-∸)
open import Util.AuxProofs using (<-cong-+ˡ)

{-
This translates a 2ADT to a VariantList.
This is correct only if the 2ADT is undead.
Otherwise, also dead variants will be part of
the resulting list.
-}
tr : ∀ {A : 𝔸} → 2ADT A → VariantList A
tr (leaf v) = v ∷ []
tr (D ⟨ l , r ⟩) = tr l ⁺++⁺ tr r

toVariantList : ∀ {A : 𝔸} → 2ADT A → VariantList A
toVariantList = tr ∘ node ∘ kill-dead

-- Converts a path to in the input 2ADT to the index in the resulting list.
conf : ∀ {A} → (e : 2ADT A) → PathConfig e → ℕ
conf .(leaf _) (.[] is-valid tleaf) = 0
conf (D ⟨ l , _ ⟩) ((_ ∷ pl) is-valid walk-left  t) = conf l (pl is-valid t)
conf (D ⟨ l , r ⟩) ((_ ∷ pr) is-valid walk-right t) = length (tr l) + conf r (pr is-valid t)

-- Converts an index from the resulting list back to a path in the input 2ADT.
fnoc : ∀ {A} → (e : 2ADT A) → ℕ → PathConfig e
fnoc (leaf v) _ = [] is-valid tleaf
fnoc (D ⟨ l , r ⟩) i with length (tr l) ≤? i
fnoc (D ⟨ l , r ⟩) i | no _ {-left-} with fnoc l i
... | pl is-valid tl = ((D ↣ true) ∷ pl) is-valid walk-left tl
fnoc (D ⟨ l , r ⟩) i | yes _  {-right-} with fnoc r (i ∸ (length (tr l)))
... | pr is-valid tr = ((D ↣ false) ∷ pr) is-valid walk-right tr

-- The index of a path will never be out of bounds.
conf-bounded : ∀ {A}
  → (e : 2ADT A)
  → (c : PathConfig e)
  → conf e c < length (tr e)
conf-bounded (leaf v) (.[] is-valid tleaf) = s≤s z≤n
conf-bounded (D ⟨ l , r ⟩) ((.D ↣ true  ∷ p) is-valid walk-left  t) = ≤-trans (conf-bounded l (p is-valid t)) (⁺++⁺-length-≤ (tr l) (tr r))
conf-bounded (D ⟨ l , r ⟩) ((.D ↣ false ∷ p) is-valid walk-right t) = go
  where
    c = p is-valid t

    -- get this by induction
    rb : conf r c < length (tr r)
    rb = conf-bounded r c

    -- add (length (tr l)) to both sides on the left
    gox : length (tr l) + conf r c < length (tr l) + length (tr r)
    gox = <-cong-+ˡ (length (tr l)) rb

    -- use the sum rule for ⁺++⁺ on the right hand side
    go : length (tr l) + conf r c < length (tr l ⁺++⁺ tr r)
    go rewrite ⁺++⁺-length (tr l) (tr r) = gox

preservation-walk-to-list-conf : ∀ {A : 𝔸}
  → (e : 2ADT A)
  → walk e ⊆[ conf e ] ⟦ tr e ⟧ₗ
preservation-walk-to-list-conf .(leaf _) (.[] is-valid tleaf) = refl
preservation-walk-to-list-conf (D ⟨ l , r ⟩) ((_ ∷ pl) is-valid walk-left t) =
  let c = pl is-valid t
  in
  begin
    walk l c
  ≡⟨ preservation-walk-to-list-conf l c ⟩
    ⟦ tr l ⟧ₗ (conf l c)
  ≡˘⟨ find-or-last-append (tr l) (tr r) (conf-bounded l c) ⟩
    ⟦ tr l ⁺++⁺ tr r ⟧ₗ (conf l c)
  ∎
preservation-walk-to-list-conf (D ⟨ l , r ⟩) ((_ ∷ pr) is-valid walk-right t) =
  let c = pr is-valid t
  in
  begin
    walk r c
  ≡⟨ preservation-walk-to-list-conf r c ⟩
    ⟦ tr r ⟧ₗ (conf r c)
  ≡˘⟨ find-or-last-prepend-+ (conf r c) (tr l) (tr r) ⟩
    ⟦ tr l ⁺++⁺ tr r ⟧ₗ (length (tr l) + (conf r c))
  ∎

preservation-walk-to-list-fnoc : ∀ {A : 𝔸}
  → (e : 2ADT A)
  → ⟦ tr e ⟧ₗ ⊆[ fnoc e ] walk e
preservation-walk-to-list-fnoc (leaf v) i = refl
preservation-walk-to-list-fnoc (D ⟨ l , r ⟩) i with length (tr l) ≤? i
... | no ¬p =
  begin
    ⟦ tr (D ⟨ l , r ⟩) ⟧ₗ i
  ≡⟨⟩
    find-or-last i ((tr l) ⁺++⁺ (tr r))
  ≡⟨ find-or-last-append (tr l) (tr r) (≰⇒> ¬p) ⟩ -- this is satisfied by eq
    find-or-last i (tr l)
  ≡⟨⟩
    ⟦ tr l ⟧ₗ i
  ≡⟨ preservation-walk-to-list-fnoc l i ⟩
    walk l (path (fnoc l i) is-valid valid (fnoc l i))
  ∎
... | yes len[tr-l]≤i  =
  begin
    ⟦ tr (D ⟨ l , r ⟩) ⟧ₗ i
  ≡⟨⟩
    find-or-last i ((tr l) ⁺++⁺ (tr r))
  ≡⟨ find-or-last-prepend-∸ (tr l) (tr r) len[tr-l]≤i ⟩
    find-or-last (i ∸ length (tr l)) (tr r)
  ≡⟨⟩
    ⟦ tr r ⟧ₗ (i ∸ length (tr l))
  ≡⟨ preservation-walk-to-list-fnoc r (i ∸ length (tr l)) ⟩
    walk r (path (fnoc r (i ∸ length (tr l))) is-valid valid (fnoc r (i ∸ length (tr l))))
  ∎

{-
This proves that 'tr' preserves walk-semantics.
This means that when we evaluate 2ADTs by just walking "randomly"
down them, then simply converting a 2ADT to a variant list by
gathering all variants in leafs from left to right preserves semantics.
-}
preservation-walk-to-list : ∀ {A : 𝔸}
  → (e : 2ADT A)
  → walk e ≅ ⟦ tr e ⟧ₗ
preservation-walk-to-list e = ≅[]→≅ (preservation-walk-to-list-conf e , preservation-walk-to-list-fnoc e)

-- 2ADTs are isomorphic to Variant Lists.
-- TODO: Construct compilers and make use of ⊕.
preservation : ∀ {A : 𝔸}
  → (e : 2ADT A)
  → ⟦ e ⟧₂ ≅ ⟦ toVariantList e ⟧ₗ
preservation e =
  ≅-begin
    ⟦ e ⟧₂
  ≅⟨ DeadElim.kill-dead-preserves e ⟩
    ⟦ kill-dead e ⟧ᵤ
  ≅⟨ Walk.preservation (kill-dead e) ⟩
    walk (node (kill-dead e))
  ≅⟨ preservation-walk-to-list (node (kill-dead e)) ⟩
    ⟦ toVariantList e ⟧ₗ
  ≅-∎

VariantList≽2ADT : VariantListL ≽ 2ADTL
VariantList≽2ADT = expressiveness-by-translation toVariantList preservation

2ADT-is-sound : Sound 2ADTL
2ADT-is-sound = soundness-by-expressiveness VariantList-is-Sound VariantList≽2ADT
