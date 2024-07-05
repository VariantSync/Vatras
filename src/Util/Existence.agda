module Util.Existence where

open import Agda.Primitive using (Level; _⊔_)
open import Data.Product using (Σ; ∄)
open import Relation.Nullary.Negation using (¬_)
open import Size using (Size; SizeUniv)

-- Existence of sizes

record Σ-Size {l : Level} (i : SizeUniv) (B : i → Set l) : Set l where
  constructor _,_
  field
    proj₁ : i
    proj₂ : B proj₁
open Σ-Size public
infixr 4 _,_ -- 4 is the same as for Σ in the standard library

∃-Size : ∀ {l : Level} {A : SizeUniv} → (A → Set l) → Set l
∃-Size = Σ-Size _

syntax ∃-Size (λ i → B) = ∃-Size[ i ] B

-- Properties (Todo: Move to own file to follow agda stdlib)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

,-injectiveʳ : ∀ {A : Set} {i j : Size} {a b : A} → (i , a) ≡ (j , b) → a ≡ b
,-injectiveʳ refl = refl

infix 2 ¬Σ-syntax
¬Σ-syntax : ∀ {a b} (A : Set a) → (A → Set b) → Set (a ⊔ b)
¬Σ-syntax _ p = ∄ p
syntax ¬Σ-syntax A (λ x → B) = ∄[ x ∈ A ] B
