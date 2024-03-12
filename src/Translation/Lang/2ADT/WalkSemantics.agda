{-
Walk semantics are equivalent to ordinary 2ADT semantics
as long as the 2ADT does not contain any dead branches.
This means that configurations can be modelled as functions or as paths.
Interestingly, we obtain a compiler that does not change the input
expression but only translates configurations.
-}
open import Framework.Definitions using (𝔽; 𝕍; 𝔸)
open import Relation.Binary using (DecidableEquality; Rel)
module Translation.Lang.2ADT.WalkSemantics
  (F : 𝔽)
  (V : 𝕍)
  (_==_ : DecidableEquality F)
  where

open import Data.Bool using (Bool; true; false; not; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.Product using (_,_)

open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (yes; no; isYes; toWitness; fromWitness; toWitnessFalse)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym)
open Eq.≡-Reasoning

open import Data.EqIndexedSet hiding (_∈_)
open Data.EqIndexedSet.≅-Reasoning

open import Framework.VariabilityLanguage
open import Lang.2ADT F V using (2ADT; leaf; _⟨_,_⟩; Configuration; ⟦_⟧)
open import Lang.2ADT.Path F V _==_
open import Translation.Lang.2ADT.DeadElim F V _==_

open import Util.Suffix

{-
Converts a configuration function to a valid path within
the given tree.
The conversion checks the configuration function at each choice,
constructs the path accordingly, and recurses until it reaches a leaf.
-}
fun-to-path : ∀ {A} (e : 2ADT A) → Configuration → PathConfig e
fun-to-path (leaf _) _ = [] is-valid tleaf
fun-to-path (D ⟨ _ , _ ⟩) c with c D
fun-to-path (D ⟨ l , _ ⟩) c | true  with fun-to-path l c
... | pl is-valid tl = ((D ↣ true)  ∷ pl) is-valid walk-left tl
fun-to-path (D ⟨ _ , r ⟩) c | false with fun-to-path r c
... | pr is-valid tr = ((D ↣ false) ∷ pr) is-valid walk-right tr

{-
Converts a path for the given tree to a function.
When the returned function is queried for the value of a feature D',
the function walks the path until it finds the respective feature in the
tree and returns the value specified in the path.
Otherwise, returns true.
(The returned function returns true for all features that
are not on a valid path.)
-}
path-to-fun : ∀ {A} (e : 2ADT A) → PathConfig e → Configuration
path-to-fun .(leaf _) ([] is-valid tleaf) _ = true
path-to-fun (.D ⟨ l , r ⟩) (((D ↣ .true) ∷ p) is-valid walk-left t) D' =
  if (isYes (D == D'))
  then true
  else path-to-fun l (p is-valid t) D'
path-to-fun (.D ⟨ l , r ⟩) (((D ↣ .false) ∷ p) is-valid walk-right t) D' =
  if (isYes (D == D'))
  then false
  else path-to-fun r (p is-valid t) D'

{-
When a given feature is not contained within a path,
then the path cannot end in a sub-path containing that feature.
TODO: There is probably a nicer, more general lemma hidden here.
-}
lem-not-endswith' : ∀ {D} {others q : Path}
  → (b : Bool)
  → All (different (D ↣ b)) others
  → ¬ (others endswith (D ↣ b ∷ q))
lem-not-endswith' b (px ∷ all) (match .(_ ↣ b ∷ _)) = toWitnessFalse px refl
lem-not-endswith' b (px ∷ all) (later ends) = lem-not-endswith' b all ends

-- more complex version of lem-not-endswith'
lem-not-endswith : ∀ {D} {others q : Path}
  → (b : Bool)
  → All (different (D ↣ b)) others
  → ¬ (((D ↣ b) ∷ others) endswith ((D ↣ not b) ∷ q))
lem-not-endswith false all (later ends) = lem-not-endswith' true all ends
lem-not-endswith true all (later ends) = lem-not-endswith' false all ends

{-
Crucial lemma for proving preservation.
path-to-fun returns the value b for a given feature D
if the path given to path-to-fun contains the selection D ↣ b somewhere.
-}
path-to-fun-lem : ∀ {A} (D : F) (e : 2ADT A) (p q : Path) (t : p starts-at e)
  → (b : Bool)
  → Unique p
  → p endswith ((D ↣ b) ∷ q)
  → path-to-fun e (p is-valid t) D ≡ b
path-to-fun-lem D (D' ⟨ _ , _ ⟩) (.D' ↣ true ∷ _) _ (walk-left  _) _ _ _ with D' == D
path-to-fun-lem _ _ _ _ _ false (u ∷ _) x | yes refl = ⊥-elim (lem-not-endswith true u x)
path-to-fun-lem _ _ _ _ _ true  _ _ | yes refl = refl
path-to-fun-lem D (_ ⟨ l , _ ⟩) (_ ∷ others) q (walk-left  t) b (_ ∷ u-o) x | no  D≠D' = path-to-fun-lem D l others q t b u-o (endswith-tail (λ where refl → D≠D' refl) x)
path-to-fun-lem D (D' ⟨ _ , _ ⟩) (D' ↣ false ∷ _) q (walk-right t) b _ x with D' == D
path-to-fun-lem _ _ _ _ _ false _ _ | yes refl = refl
path-to-fun-lem _ _ _ _ _ true  (u ∷ _) x | yes refl = ⊥-elim (lem-not-endswith false u x)
path-to-fun-lem D (_ ⟨ _ , r ⟩) (_ ∷ others) q (walk-right  t) b (_ ∷ u-o) x | no  D≠D' = path-to-fun-lem D r others q t b u-o (endswith-tail (λ where refl → D≠D' refl) x)

{-
If a path p ends in a sub-path with a certain selection,
that selection is within p, too.
-}
endswith-path-contains : ∀ {p q : Path} {D}
  → (b : Bool)
  → p endswith ((D ↣ b) ∷ q)
  → D ∈ p
endswith-path-contains _ (match .((_ ↣ _) ∷ _)) = here (fromWitness refl)
endswith-path-contains b (later x) = there (endswith-path-contains b x)

path-to-fun-step-l-inner2 : ∀ {A}
  → (D : F) (l r : 2ADT A)
  → (p : Path) → (t : p starts-at l)
  → All (different (D ↣ true)) p
    -------------------------------------------------------------------
  → (E : F) → (E ∈ p)
  →   path-to-fun (D ⟨ l , r ⟩) ((D ↣ true ∷ p) is-valid walk-left t) E
    ≡ path-to-fun l (p is-valid t) E
path-to-fun-step-l-inner2 D l r p t all-dims-in-p-different-to-D E E∈p with D == E
... | yes refl = ⊥-elim (All-different→∉ true p all-dims-in-p-different-to-D E∈p)
... | no _ = refl

-- clone-and-own from path-to-fun-step-l-inner2
path-to-fun-step-r-inner2 : ∀ {A}
  → (D : F) (l r : 2ADT A)
  → (p : Path) → (t : p starts-at r)
  → All (different (D ↣ false)) p
    -------------------------------------------------------------------
  → (E : F) → (E ∈ p)
  →   path-to-fun (D ⟨ l , r ⟩) ((D ↣ false ∷ p) is-valid walk-right t) E
    ≡ path-to-fun r (p is-valid t) E
path-to-fun-step-r-inner2 D l r p t all-dims-in-p-different-to-D E E∈p with D == E
... | yes refl = ⊥-elim (All-different→∉ true p all-dims-in-p-different-to-D E∈p)
... | no _ = refl

path-to-fun-step-l-inner : ∀ {A}
  -- for a choice D ⟨ l , r ⟩
  → (D : F) (l r : 2ADT A)
  → (lp : Path)
  -- if there is a subexpression e
  → (e : 2ADT A) (ep : Path)
  -- (i.e., all paths starting in l end in paths starting in e)
  → (tlp : lp starts-at l)
  → (tep : ep starts-at e)
  → (sub : lp endswith ep)
  -- and if the left branch l is undead
  → All (different (D ↣ true)) lp -- this also means All (different (D ↣ true)) ep
  → Unique lp
  -- then it does not matter whether we convert the whole path from the choice to
  -- a function, or if we start at the left alternative below.
  →   ⟦ e ⟧ (path-to-fun (D ⟨ l , r ⟩) ((D ↣ true ∷ lp) is-valid walk-left tlp))
    ≡ ⟦ e ⟧ (path-to-fun l (lp is-valid tlp))
path-to-fun-step-l-inner D l r lp (leaf v) ep tlp tep sub x _ = refl
path-to-fun-step-l-inner D l r lp (D' ⟨ a , b ⟩) ((.D' ↣ .true) ∷ ep) tlp (walk-left tep) sub x u =
  begin
    ⟦ D' ⟨ a , b ⟩ ⟧ c-big
  ≡⟨⟩
    (if c-big D' then ⟦ a ⟧ c-big else ⟦ b ⟧ c-big)
  ≡⟨ Eq.cong (if_then ⟦ a ⟧ c-big else ⟦ b ⟧ c-big) (path-to-fun-step-l-inner2 D l r lp tlp x D' (endswith-Any sub (here (fromWitness refl)))) ⟩
    (if c-sml D' then ⟦ a ⟧ c-big else ⟦ b ⟧ c-big)
  ≡⟨ lem ⟩
    (if c-sml D' then ⟦ a ⟧ c-sml else ⟦ b ⟧ c-sml)
  ≡⟨⟩
    ⟦ D' ⟨ a , b ⟩ ⟧ c-sml
  ∎
  where
    c-big = λ D'' → if isYes (D == D'') then true else path-to-fun l (lp is-valid tlp) D''
    c-sml = path-to-fun l (lp is-valid tlp)

    force : c-sml D' ≡ true
    force = path-to-fun-lem D' l lp ep tlp true u sub

    lem : (if c-sml D' then ⟦ a ⟧ c-big else ⟦ b ⟧ c-big) ≡ (if c-sml D' then ⟦ a ⟧ c-sml else ⟦ b ⟧ c-sml)
    lem rewrite force = path-to-fun-step-l-inner D l r lp a ep tlp tep (endswith-shrink-suffix sub) x u
path-to-fun-step-l-inner D l r lp (D' ⟨ a , b ⟩) ((.D' ↣ false) ∷ ep) tlp (walk-right tep) sub x u
  -- These rewrites are copied from the case above.
  rewrite path-to-fun-step-l-inner2 D l r lp tlp x D' (endswith-Any sub (here (fromWitness refl)))
  rewrite path-to-fun-lem D' l lp ep tlp false u sub
  rewrite path-to-fun-step-l-inner D l r lp b ep tlp tep (endswith-shrink-suffix sub) x u
  = refl

-- This is a huge copy and paste blob from
-- path-to-fun-step-r-inner
path-to-fun-step-r-inner : ∀ {A}
  → (D : F) (l r : 2ADT A)
  → (rp : Path)
  → (e : 2ADT A) (ep : Path)
  → (trp : rp starts-at r)
  → (tep : ep starts-at e)
  → (sub : rp endswith ep)
  → All (different (D ↣ false)) rp
  → Unique rp
  →   ⟦ e ⟧ (path-to-fun (D ⟨ l , r ⟩) ((D ↣ false ∷ rp) is-valid walk-right trp))
    ≡ ⟦ e ⟧ (path-to-fun r (rp is-valid trp))
path-to-fun-step-r-inner D l r lp (leaf v) ep tlp tep sub x _ = refl
path-to-fun-step-r-inner D l r lp (D' ⟨ a , b ⟩) ((.D' ↣ .true) ∷ ep) tlp (walk-left tep) sub x u
  rewrite path-to-fun-step-r-inner2 D l r lp tlp x D' (endswith-Any sub (here (fromWitness refl)))
  rewrite path-to-fun-lem D' r lp ep tlp true u sub
  rewrite path-to-fun-step-r-inner D l r lp a ep tlp tep (endswith-shrink-suffix sub) x u
  = refl
path-to-fun-step-r-inner D l r lp (D' ⟨ a , b ⟩) ((.D' ↣ false) ∷ ep) tlp (walk-right tep) sub x u
  -- These rewrites are copied from the case above.
  rewrite path-to-fun-step-r-inner2 D l r lp tlp x D' (endswith-Any sub (here (fromWitness refl)))
  rewrite path-to-fun-lem D' r lp ep tlp false u sub
  rewrite path-to-fun-step-r-inner D l r lp b ep tlp tep (endswith-shrink-suffix sub) x u
  = refl

path-to-fun-step-l : ∀ {A}
  → (D : F) (l r : 2ADT A)
  → Undead (D ⟨ l , r ⟩)
  → (p : Path)
  → (t : p starts-at l)
  →   ⟦ l ⟧ (path-to-fun (D ⟨ l , r ⟩) ((D ↣ true ∷ p) is-valid walk-left t))
    ≡ ⟦ l ⟧ (path-to-fun l (p is-valid t))
path-to-fun-step-l D l r u p t with u ((D ↣ true) ∷ p) (walk-left t)
... | u ∷ uu = path-to-fun-step-l-inner D l r p l p t t (match p) u uu

path-to-fun-step-r : ∀ {A}
  → (D : F) (l r : 2ADT A)
  → Undead (D ⟨ l , r ⟩)
  → (p : Path)
  → (t : p starts-at r)
  →   ⟦ r ⟧ (path-to-fun (D ⟨ l , r ⟩) ((D ↣ false ∷ p) is-valid walk-right t))
    ≡ ⟦ r ⟧ (path-to-fun r (p is-valid t))
path-to-fun-step-r D l r u p t with u ((D ↣ false) ∷ p) (walk-right t)
... | u ∷ uu = path-to-fun-step-r-inner D l r p r p t t (match p) u uu

path-to-fun-head : ∀ {A}
  → (D : F)
  → (l r : 2ADT A)
  → (b : Bool)
  → (p : Path)
  → (t : ((D ↣ b) ∷ p) starts-at (D ⟨ l , r ⟩))
  → path-to-fun (D ⟨ l , r ⟩) (((D ↣ b) ∷ p) is-valid t) D ≡ b
path-to-fun-head D l r .true p (walk-left t) with D == D
... | yes D≡D = refl
... | no  D≢D = ⊥-elim (D≢D refl)
path-to-fun-head D l r .false p (walk-right t) with D == D
... | yes D≡D = refl
... | no  D≢D = ⊥-elim (D≢D refl)

preservation-path-configs-conf : ∀ {A : 𝔸}
  → (e : 2ADT A)
  → (u : Undead e)
  → ⟦ e ⊚ u ⟧ᵤ ⊆[ fun-to-path e ] walk e
preservation-path-configs-conf (leaf _) _ _ = refl
preservation-path-configs-conf (D ⟨ _ , _ ⟩) _ c with c D
preservation-path-configs-conf (_ ⟨ l , _ ⟩) u c | true  with fun-to-path l c in eq
... | pl is-valid tl =
  begin
    ⟦ l ⟧ c
  ≡⟨⟩
    ⟦ l ⊚ undead-left u ⟧ᵤ c
  ≡⟨ preservation-path-configs-conf l (undead-left u) c ⟩
    walk l (fun-to-path l c)
  ≡⟨ Eq.cong (walk l) eq ⟩
    walk l (pl is-valid tl)
  ∎
preservation-path-configs-conf (_ ⟨ _ , r ⟩) u c | false with fun-to-path r c in eq
... | _ rewrite (sym eq) = preservation-path-configs-conf r (undead-right u) c

preservation-path-configs-fnoc : ∀ {A : 𝔸}
  → (e : 2ADT A)
  → (u : Undead e)
  → walk e ⊆[ path-to-fun e ] ⟦ e ⊚ u ⟧ᵤ
preservation-path-configs-fnoc (leaf v) _ (.[] is-valid tleaf) = refl
preservation-path-configs-fnoc (D ⟨ l , r ⟩) u c@((.(D ↣ true ) ∷ p) is-valid walk-left t)
  rewrite path-to-fun-head D l r true p (walk-left t) =
  begin
    walk l (p is-valid t)
  ≡⟨ preservation-path-configs-fnoc l (undead-left u) (p is-valid t) ⟩
    ⟦ l ⟧ (path-to-fun l (p is-valid t))
  ≡˘⟨ path-to-fun-step-l D l r u p t ⟩
    ⟦ l ⟧ (path-to-fun (D ⟨ l , r ⟩) ((D ↣ true ∷ p) is-valid walk-left t))
  ≡⟨⟩
    ⟦ l ⟧ (λ D' → if isYes (D == D') then true else path-to-fun l (p is-valid t) D')
  ∎
preservation-path-configs-fnoc (D ⟨ l , r ⟩) u ((.(D ↣ false) ∷ p) is-valid walk-right t)
  rewrite path-to-fun-head D l r false p (walk-right t)
  rewrite preservation-path-configs-fnoc r (undead-right u) (p is-valid t)
  rewrite path-to-fun-step-r D l r u p t
  = refl

preservation : ∀ {A : 𝔸}
  → (e : Undead2ADT A)
  → ⟦ e ⟧ᵤ ≅ walk (node e)
preservation e = ≅[]→≅ (
    preservation-path-configs-conf (node e) (undead e)
  , preservation-path-configs-fnoc (node e) (undead e))
