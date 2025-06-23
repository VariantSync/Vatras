open import Data.Nat using (ℕ; _+_; _<_)

module Vatras.Util.ProxyInduction
    {ℓ₁ ℓ₂}
    {A : Set ℓ₁}
    (size : A → ℕ) -- i.e., the proxy
    (P : A → Set ℓ₂)
  where

open import Axiom.Extensionality.Propositional using (Extensionality; lower-extensionality)
open import Data.Nat.Induction using (<-wellFounded)
open import Induction using (build)
open import Induction.WellFounded
open import Level using (zero; _⊔_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

Step : Set (ℓ₁ ⊔ ℓ₂)
Step =
  ∀ (a : A)
  → (rec : ∀ (b : A) → size b < size a → P b)
  → P a

induction
  : (step : Step)
  → (a : A) → P a
induction step a = All.wfRec <-wellFounded (ℓ₁ ⊔ ℓ₂) Q step' (size a) a refl
  module induction-Implementation where
  Q : ℕ → Set (ℓ₁ ⊔ ℓ₂)
  Q n = ∀ (b : A) → size b ≡ n → P b

  step' : (n : ℕ) → (∀ {m} → m < n → Q m) → Q n
  step' n rec b size-b≡n = step b (λ c c<b → rec {size c} (Eq.subst (size c <_) size-b≡n c<b) c refl)

RecIrrelevant : Step → Set (ℓ₁ ⊔ ℓ₂)
RecIrrelevant step =
  ∀ (a : A)
  → {rec₁ rec₂ : ∀ (b : A) → size b < size a → P b}
  → (rec-equivalent : ∀ b b<a → rec₁ b b<a ≡ rec₂ b b<a)
  → step a rec₁ ≡ step a rec₂

induction-step
  : (step : Step)
  → RecIrrelevant step
  → (a : A)
  → induction step a ≡ step a (λ b _ → induction step b)
induction-step step rec-irrelevant a =
    induction step a
  ≡⟨⟩
    All.wfRec <-wellFounded _ Q step' (size a) a refl
  ≡⟨⟩
    build (All.wfRecBuilder <-wellFounded _) Q step' (size a) a refl
  ≡⟨⟩
    step' (size a) (All.wfRecBuilder <-wellFounded _ Q step' (size a)) a refl
  ≡⟨⟩
    step a (λ b b<a → All.wfRecBuilder <-wellFounded _ Q step' (size a) (Eq.subst (size b <_) refl b<a) b refl)
  ≡⟨⟩
    step a (λ b b<a → Some.wfRecBuilder Q step' (size a) (<-wellFounded (size a)) (Eq.subst (size b <_) refl b<a) b refl)
  ≡⟨⟩
    step a (λ b b<a → step' (size b) (Some.wfRecBuilder Q step' (size b) (acc-inverse (<-wellFounded (size a)) (Eq.subst (size b <_) refl b<a))) b refl)
  ≡⟨⟩
    step a (λ b b<a → step b (λ c c<b → Some.wfRecBuilder Q step' (size b) (acc-inverse (<-wellFounded (size a)) (Eq.subst (size b <_) refl b<a)) (Eq.subst (size c <_) refl c<b) c refl))
  ≡⟨ rec-irrelevant a (λ b b<a → rec-irrelevant b (λ c c<b → lemma b c c<b (acc-inverse (<-wellFounded (size a)) (Eq.subst (size b <_) refl b<a)) (<-wellFounded (size b)))) ⟩
    step a (λ b _ → step b (λ c c<b → Some.wfRecBuilder Q step' (size b) (<-wellFounded (size b)) (Eq.subst (size c <_) refl c<b) c refl))
  ≡⟨⟩
    step a (λ b _ → step b (λ c c<b → All.wfRecBuilder <-wellFounded _ Q step' (size b) (Eq.subst (size c <_) refl c<b) c refl))
  ≡⟨⟩
    step a (λ b _ → step' (size b) (All.wfRecBuilder <-wellFounded _ Q step' (size b)) b refl)
  ≡⟨⟩
    step a (λ b _ → build (All.wfRecBuilder <-wellFounded _) Q step' (size b) b refl)
  ≡⟨⟩
    step a (λ b _ → All.wfRec <-wellFounded _ Q step' (size b) b refl)
  ≡⟨⟩
    step a (λ b _ → induction step b)
  ∎
  where
  open Eq.≡-Reasoning
  open induction-Implementation step a

  lemma : ∀ b c c<b acc₁ acc₂
    → Some.wfRecBuilder Q step' (size b) acc₁ (Eq.subst (size c <_) refl c<b) c refl
    ≡ Some.wfRecBuilder Q step' (size b) acc₂ (Eq.subst (size c <_) refl c<b) c refl
  lemma b c c<b (acc acc₁) (acc acc₂) =
      Some.wfRecBuilder Q step' (size b) (acc acc₁) (Eq.subst (size c <_) refl c<b) c refl
    ≡⟨⟩
      step' (size c) (Some.wfRecBuilder Q step' (size c) (acc₁ c<b)) c refl
    ≡⟨⟩
      step c (λ d d<c → Some.wfRecBuilder Q step' (size c) (acc₁ c<b) (Eq.subst (size d <_) refl d<c) d refl)
    ≡⟨ rec-irrelevant c (λ d d<c → lemma c d d<c (acc₁ c<b) (acc₂ c<b)) ⟩
      step c (λ d d<c → Some.wfRecBuilder Q step' (size c) (acc₂ c<b) (Eq.subst (size d <_) refl d<c) d refl)
    ≡⟨⟩
      step' (size c) (Some.wfRecBuilder Q step' (size c) (acc₂ c<b)) c refl
    ≡⟨⟩
      Some.wfRecBuilder Q step' (size b) (acc acc₂) (Eq.subst (size c <_) refl c<b) c refl
    ∎

induction-step-with-extensionality
  : Extensionality ℓ₁ ℓ₂
  → (step : Step)
  → (a : A)
  → induction step a ≡ step a (λ b _ → induction step b)
induction-step-with-extensionality fun-ext step =
  induction-step step λ a step-ext →
    Eq.cong (step a) (fun-ext (λ a → lower-extensionality ℓ₁ ℓ₂ fun-ext (step-ext a)))
