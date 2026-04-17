module Vatras.Util.Big-O where

open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s; z≤n; _*_; _^_)
import Data.Nat.Properties as ℕ
open import Data.Product using (_,_; Σ-syntax)
open import Function using (id)
import Relation.Binary.PropositionalEquality as Eq
open import Relation.Unary using (_∈_)

𝒪[_] : (ℕ → ℕ) → (ℕ → ℕ) → Set
𝒪[ g ] f = Σ[ n ∈ ℕ ] ∀ m → f m ≤ n * g m

𝒪-transitive : (f g h : ℕ → ℕ) → f ∈ 𝒪[ g ] → g ∈ 𝒪[ h ] → f ∈ 𝒪[ h ]
𝒪-transitive f g h (m₁ , f≤g) (m₂ , f≤h) = m₁ * m₂ , λ n →
  begin
    f n
  ≤⟨ f≤g n ⟩
    m₁ * g n
  ≤⟨ ℕ.*-monoʳ-≤ m₁ (f≤h n) ⟩
    m₁ * (m₂ * h n)
  ≡⟨ ℕ.*-assoc m₁ m₂ (h n) ⟨
    m₁ * m₂ * h n
  ∎
  where
  open ℕ.≤-Reasoning

module ReferenceFunctions where
  n : ℕ → ℕ
  n = id

  n^2 : ℕ → ℕ
  n^2 n = n ^ 2

  2^n : ℕ → ℕ
  2^n n = 2 ^ n

module Specializations where
  𝒪[n] : (ℕ → ℕ) → Set
  𝒪[n] = 𝒪[ ReferenceFunctions.n ]

  𝒪[n^2] : (ℕ → ℕ) → Set
  𝒪[n^2] = 𝒪[ ReferenceFunctions.n^2 ]

  𝒪[2^n] : (ℕ → ℕ) → Set
  𝒪[2^n] = 𝒪[ ReferenceFunctions.2^n ]

module Examples where
  open ReferenceFunctions

  n∈𝒪[n] : id ∈ 𝒪[ n ]
  n∈𝒪[n] = 1 , λ n → ℕ.≤-reflexive (Eq.sym (ℕ.*-identityˡ n))

  n∈𝒪[n^2] : n ∈ 𝒪[ n^2 ]
  n∈𝒪[n^2] = 1 , λ
    where
      zero → ℕ.≤-refl
      (suc n) →
        begin
          suc n
        ≡⟨ ℕ.^-identityʳ (suc n) ⟨
          suc n ^ 1
        ≤⟨ ℕ.^-monoʳ-≤ (suc n) (s≤s (z≤n {n = 1})) ⟩
          suc n ^ 2
        ≡⟨ ℕ.*-identityˡ (suc n ^ 2) ⟨
          1 * suc n ^ 2
        ∎
    where
    open ℕ.≤-Reasoning
