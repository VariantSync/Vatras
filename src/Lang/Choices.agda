{-# OPTIONS --sized-types #-}
module Lang.Choices where

open import Data.Fin using (Fin)
open import Data.List as List using (List)
open import Data.List.NonEmpty using (List⁺)
open import Data.Nat using (ℕ; zero)
open import Data.Vec as Vec using (Vec)
open import Size using (Size; ↑_)
open import Util.List using (find-or-last)
open import Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs)

data ArbitraryChoice (D A : Set) : {Size} → Set where
  artifact : {i : Size} → A → List (ArbitraryChoice D A {i}) → ArbitraryChoice D A {↑ i}
  choice : {i : Size} → D → List⁺ (ArbitraryChoice D A {i}) → ArbitraryChoice D A {↑ i}

data NAryChoice (n : ℕ≥ 2) (D A : Set) : {Size} → Set where
  artifact : {i : Size} → A → List (NAryChoice n D A {i}) → NAryChoice n D A {↑ i}
  choice : {i : Size} → D → Vec (NAryChoice n D A {i}) (ℕ≥.toℕ n) → NAryChoice n D A {↑ i}

2AryChoice = NAryChoice (sucs zero)


ArbitraryChoiceConfig : Set → Set
ArbitraryChoiceConfig D = D → ℕ

NAryChoiceConfig : ℕ≥ 2 → Set → Set
NAryChoiceConfig n D = D → Fin (ℕ≥.toℕ n)

2AryChoiceConfig : Set → Set
2AryChoiceConfig = NAryChoiceConfig (sucs zero)


data Variant (A : Set) : Set where
  artifact : A → List (Variant A) → Variant A

⟦_⟧ₐ : {i : Size} → {D A : Set} → ArbitraryChoice D A {i} → ArbitraryChoiceConfig D → Variant A
⟦ artifact a cs ⟧ₐ config = artifact a (List.map (λ e → ⟦ e ⟧ₐ config) cs)
⟦ choice d cs ⟧ₐ config = ⟦ find-or-last (config d) cs ⟧ₐ config

⟦_⟧ₙ : {i : Size} → {n : ℕ≥ 2} → {D A : Set} → NAryChoice n D A {i} → NAryChoiceConfig n D → Variant A
⟦ artifact a cs ⟧ₙ config = artifact a (List.map (λ e → ⟦ e ⟧ₙ config) cs)
⟦_⟧ₙ {n = sucs n} (choice d cs) config = ⟦ Vec.lookup cs (config d) ⟧ₙ config

⟦_⟧₂ : {i : Size} → {D A : Set} → 2AryChoice D A {i} → 2AryChoiceConfig D → Variant A
⟦_⟧₂ = ⟦_⟧ₙ {n = sucs zero}
