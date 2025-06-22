open import Vatras.Framework.Definitions
module Vatras.Lang.ADT.Merge
  (F : 𝔽) (V : 𝕍)
  (_+ᵥ_ : ∀ {A} → V A → V A → V A)
  where
open import Data.Bool using (Bool; if_then_else_; true; false)
open import Data.Bool.Properties using (if-float)
open import Relation.Binary.PropositionalEquality using (refl; _≡_; _≗_)
open Relation.Binary.PropositionalEquality.≡-Reasoning

open import Vatras.Lang.ADT F V
open import Vatras.Framework.Relation.Expression V
open import Vatras.Util.AuxProofs using (if-cong; if-swap)

{-|
Merges two ADTs.
The resulting ADT denotes all possible compositions of variants, such that configuring the resulting ADT
is equivalent to configuring both input ADTs and composing the resulting variants (see ⊕-spec below).
This operations inherits all properties of the variant composition (e.g., commutativity, associativity etc).
-}
_⊕_ : ∀ {A} → ADT A → ADT A → ADT A
leaf l          ⊕ leaf r          = leaf (l +ᵥ r)
leaf l          ⊕ (E ⟨ el , er ⟩) = E ⟨ leaf l ⊕ el , leaf l ⊕ er ⟩
(D ⟨ dl , dr ⟩) ⊕ leaf r          = D ⟨ dl ⊕ leaf r , dr ⊕ leaf r ⟩
(D ⟨ dl , dr ⟩) ⊕ (E ⟨ el , er ⟩) = D ⟨ E ⟨ dl ⊕ el , dl ⊕ er ⟩ , E ⟨ dr ⊕ el , dr ⊕ er ⟩ ⟩

⊕-spec : ∀ {A} (l r : ADT A) (c : Configuration) →
   ⟦ l ⊕ r ⟧ c ≡ ⟦ l ⟧ c +ᵥ ⟦ r ⟧ c
⊕-spec (leaf l)        (leaf r       ) c = refl
⊕-spec (leaf l)        (E ⟨ el , er ⟩) c =
  -- We have to prove one case directly (i.e., without "with" or "rewrite") for termination checking.
    ⟦ E ⟨ leaf l ⊕ el , leaf l ⊕ er ⟩ ⟧ c
  ≡⟨⟩
    (if c E then ⟦ leaf l ⊕ el ⟧ c else ⟦ leaf l ⊕ er ⟧ c)
  ≡⟨ if-cong (c E) (⊕-spec (leaf l) el c) (⊕-spec (leaf l) er c) ⟩
    (if c E
     then ⟦ leaf l ⟧ c +ᵥ ⟦ el ⟧ c
     else ⟦ leaf l ⟧ c +ᵥ ⟦ er ⟧ c)
  ≡⟨⟩
    (if c E
     then l +ᵥ ⟦ el ⟧ c
     else l +ᵥ ⟦ er ⟧ c)
  ≡⟨ if-float (l +ᵥ_) (c E) ⟨
    l +ᵥ (if c E then ⟦ el ⟧ c else ⟦ er ⟧ c)
  ≡⟨⟩
    ⟦ leaf l ⟧ c +ᵥ ⟦ E ⟨ el , er ⟩ ⟧ c
  ∎
⊕-spec (D ⟨ dl , dr ⟩) (leaf r       ) c with c D
... | true  = ⊕-spec dl (leaf r) c
... | false = ⊕-spec dr (leaf r) c
⊕-spec (D ⟨ dl , dr ⟩) (E ⟨ el , er ⟩) c with c D | c E
... | true  | true  = ⊕-spec dl el c
... | true  | false = ⊕-spec dl er c
... | false | true  = ⊕-spec dr el c
... | false | false = ⊕-spec dr er c

-- properties

⊕-comm :
  (∀ {A} (v w : V A) → v +ᵥ w ≡ w +ᵥ v) →
  ---------------------------------------------
  (∀ {A} (l r : ADT A) → ⟦ l ⊕ r ⟧ ≗ ⟦ r ⊕ l ⟧)
⊕-comm +ᵥ-comm (leaf l       ) (leaf r       ) _ = +ᵥ-comm l r
⊕-comm +ᵥ-comm (leaf l       ) (E ⟨ el , er ⟩) c =
    ⟦ E ⟨ leaf l ⊕ el , leaf l ⊕ er ⟩ ⟧ c
  ≡⟨⟩
    (if c E then ⟦ leaf l ⊕ el ⟧ c else ⟦ leaf l ⊕ er ⟧ c)
  ≡⟨ if-cong (c E) (⊕-comm +ᵥ-comm (leaf l) el c) (⊕-comm +ᵥ-comm (leaf l) er c) ⟩
    (if c E then ⟦ el ⊕ leaf l ⟧ c else ⟦ er ⊕ leaf l ⟧ c)
  ≡⟨⟩
    ⟦ E ⟨ el ⊕ leaf l , er ⊕ leaf l ⟩ ⟧ c
  ∎
⊕-comm +ᵥ-comm (D ⟨ dl , dr ⟩) (leaf r       ) c
  rewrite ⊕-comm +ᵥ-comm dl (leaf r) c
        | ⊕-comm +ᵥ-comm dr (leaf r) c
        = refl
⊕-comm +ᵥ-comm (D ⟨ dl , dr ⟩) (E ⟨ el , er ⟩) c with c D | c E
... | true  | true  = ⊕-comm +ᵥ-comm dl el c
... | true  | false = ⊕-comm +ᵥ-comm dl er c
... | false | true  = ⊕-comm +ᵥ-comm dr el c
... | false | false = ⊕-comm +ᵥ-comm dr er c
