{-|
This module generates a list of variants from an `ADT` expression by choosing
all possible configurations for each choice. However, this simple process might
result in impossible, dead variants. Hence, dead branch elimination is applied
first, resulting in the correct list of variants.
-}
open import Framework.Definitions using (𝔽; 𝕍; 𝔸)
open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Relation.Binary using (DecidableEquality; Rel)
module Translation.Lang.ADT-to-VariantList
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
open Data.EqIndexedSet.≅[]-Reasoning

open import Framework.VariabilityLanguage
open import Framework.Compiler
open import Framework.Relation.Expressiveness V using (_≽_; expressiveness-from-compiler)
open import Framework.Properties.Soundness V using (Sound)
open import Framework.Proof.ForFree V using (soundness-by-expressiveness)
open import Lang.ADT
  using (ADT; ADTL; leaf; _⟨_,_⟩)
  renaming (⟦_⟧ to ⟦_⟧₂; Configuration to Conf₂)
open import Lang.VariantList V
  using (VariantList; VariantListL; VariantList-is-Sound)
  renaming (⟦_⟧ to ⟦_⟧ₗ; Configuration to Confₗ)

open import Lang.ADT.Path F V _==_
open import Translation.Lang.ADT.DeadElim F V _==_ as DeadElim using (node; kill-dead; ⟦_⟧ᵤ; UndeadADT; UndeadADTL)
open import Translation.Lang.ADT.WalkSemantics F V _==_ as Walk using ()

open import Util.List using (find-or-last; ⁺++⁺-length; ⁺++⁺-length-≤; find-or-last-append; find-or-last-prepend-+; find-or-last-prepend-∸)
open import Util.AuxProofs using (<-cong-+ˡ)

{-
This translates a ADT to a VariantList.
This is correct only if the ADT is undead.
Otherwise, also dead variants will be part of
the resulting list.
-}
tr : ∀ {A : 𝔸} → ADT V F A → VariantList A
tr (leaf v) = v ∷ []
tr (D ⟨ l , r ⟩) = tr l ⁺++⁺ tr r

tr-undead : ∀ {A : 𝔸} → UndeadADT A → VariantList A
tr-undead = tr ∘ node

toVariantList : ∀ {A : 𝔸} → ADT V F A → VariantList A
toVariantList = tr-undead ∘ kill-dead

-- Converts a path to in the input ADT to the index in the resulting list.
conf : ∀ {A} → (e : ADT V F A) → PathConfig e → ℕ
conf .(leaf _) (.[] is-valid tleaf) = 0
conf (D ⟨ l , _ ⟩) ((_ ∷ pl) is-valid walk-left  t) = conf l (pl is-valid t)
conf (D ⟨ l , r ⟩) ((_ ∷ pr) is-valid walk-right t) = length (tr l) + conf r (pr is-valid t)

-- Converts an index from the resulting list back to a path in the input ADT.
fnoc : ∀ {A} → (e : ADT V F A) → ℕ → PathConfig e
fnoc (leaf v) _ = [] is-valid tleaf
fnoc (D ⟨ l , r ⟩) i with length (tr l) ≤? i
fnoc (D ⟨ l , r ⟩) i | no _ {-left-} with fnoc l i
... | pl is-valid tl = ((D ↣ true) ∷ pl) is-valid walk-left tl
fnoc (D ⟨ l , r ⟩) i | yes _  {-right-} with fnoc r (i ∸ (length (tr l)))
... | pr is-valid tr = ((D ↣ false) ∷ pr) is-valid walk-right tr

-- The index of a path will never be out of bounds.
conf-bounded : ∀ {A}
  → (e : ADT V F A)
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
  → (e : ADT V F A)
  → walk e ⊆[ conf e ] ⟦ tr e ⟧ₗ
preservation-walk-to-list-conf .(leaf _) (.[] is-valid tleaf) = refl
preservation-walk-to-list-conf (D ⟨ l , r ⟩) ((_ ∷ pl) is-valid walk-left t) =
  let c = pl is-valid t
  in
  begin
    walk l c
  ≡⟨ preservation-walk-to-list-conf l c ⟩
    ⟦ tr l ⟧ₗ (conf l c)
  ≡⟨ find-or-last-append (tr l) (tr r) (conf-bounded l c) ⟨
    ⟦ tr l ⁺++⁺ tr r ⟧ₗ (conf l c)
  ∎
preservation-walk-to-list-conf (D ⟨ l , r ⟩) ((_ ∷ pr) is-valid walk-right t) =
  let c = pr is-valid t
  in
  begin
    walk r c
  ≡⟨ preservation-walk-to-list-conf r c ⟩
    ⟦ tr r ⟧ₗ (conf r c)
  ≡⟨ find-or-last-prepend-+ (conf r c) (tr l) (tr r) ⟨
    ⟦ tr l ⁺++⁺ tr r ⟧ₗ (length (tr l) + (conf r c))
  ∎

preservation-walk-to-list-fnoc : ∀ {A : 𝔸}
  → (e : ADT V F A)
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
This means that when we evaluate ADTs by just walking "randomly"
down them, then simply converting a ADT to a variant list by
gathering all variants in leafs from left to right preserves semantics.
-}
preservation-walk-to-list : ∀ {A : 𝔸}
  → (e : ADT V F A)
  → walk e ≅[ conf e ][ fnoc e ] ⟦ tr e ⟧ₗ
preservation-walk-to-list e = (preservation-walk-to-list-conf e , preservation-walk-to-list-fnoc e)

conf-undead-to-list : ∀ {A} → UndeadADT A → Conf₂ F → ℕ
conf-undead-to-list e = conf (node e) ∘ Walk.fun-to-path (node e)

fnoc-undead-to-list : ∀ {A} → UndeadADT A → ℕ → Conf₂ F
fnoc-undead-to-list e = Walk.path-to-fun (node e) ∘ fnoc (node e)

preservation-undead-to-list : ∀ {A : 𝔸}
  → (e : UndeadADT A)
  → ⟦ e ⟧ᵤ ≅[ conf-undead-to-list e ][ fnoc-undead-to-list e ] ⟦ tr-undead e ⟧ₗ
preservation-undead-to-list e =
  ≅[]-begin
    ⟦ e ⟧ᵤ
  ≅[]⟨ Walk.preservation e ⟩
    walk (node e)
  ≅[]⟨ preservation-walk-to-list (node e) ⟩
    ⟦ tr-undead e ⟧ₗ
  ≅[]-∎

UndeadADT→VariantList : LanguageCompiler UndeadADTL VariantListL
UndeadADT→VariantList = record
  { compile = tr-undead
  ; config-compiler = λ e → record
    { to = conf-undead-to-list e
    ; from = fnoc-undead-to-list e
    }
  ; preserves = preservation-undead-to-list
  }

ADT→VariantList : LanguageCompiler (ADTL V F) VariantListL
ADT→VariantList = DeadElim.kill-dead-compiler ⊕ UndeadADT→VariantList

VariantList≽ADT : VariantListL ≽ ADTL V F
VariantList≽ADT = expressiveness-from-compiler ADT→VariantList

ADT-is-sound : Sound (ADTL V F)
ADT-is-sound = soundness-by-expressiveness VariantList-is-Sound VariantList≽ADT
