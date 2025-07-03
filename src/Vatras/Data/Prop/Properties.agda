module Vatras.Data.Prop.Properties {F : Set} where

import Data.Bool as Bool
open import Data.Bool.Properties using (∧-comm; ∧-zeroʳ)
open import Data.Empty using (⊥)
open import Data.Product as Product using (Σ; _×_; ∃-syntax; _,_)
open import Data.Sum as Sum using (_⊎_) renaming (inj₁ to left; inj₂ to right)

open import Relation.Nullary.Negation renaming (¬_ to never)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; sym; trans)
open Eq.≡-Reasoning

open import Vatras.Data.Prop
open import Vatras.Util.AuxProofs using (true≢false)

all-true : Assignment F
all-true _ = Bool.true

all-false : Assignment F
all-false _ = Bool.false

NonContradiction :
  ∀ {b} {p : Prop F} (a : Assignment F)
  → eval    p  a ≡ b
  → eval (¬ p) a ≡ Bool.not b
NonContradiction _ eq = cong Bool.not eq

NonContradiction' :
  ∀ (p : Prop F) (a : Assignment F)
  → eval p a ≡ Bool.true
  → eval p a ≡ Bool.false
  → ⊥
NonContradiction' _ _ t f = true≢false (trans (sym f) t) refl

Satisfying : Prop F → Assignment F → Set
Satisfying p a = eval p a ≡ Bool.true

Unsatisfying : Prop F → Assignment F → Set
Unsatisfying p a = eval p a ≡ Bool.false

Satisfiable : Prop F → Set
Satisfiable p = Σ (Assignment F) (Satisfying p)

Falsifiable : Prop F → Set
Falsifiable p = Σ (Assignment F) (Unsatisfying p)

Tautology : Prop F → Set
Tautology p = ∀ a → Satisfying p a

Contradiction : Prop F → Set
Contradiction p = ∀ a → Unsatisfying p a

Const : Prop F → Set
Const p = Tautology p ⊎ Contradiction p

Const' : Prop F → Set
Const' p = ∃[ b ] (∀ a → eval p a ≡ b)

Const→Const' : ∀ {p} → Const p → Const' p
Const→Const' (left  taut ) = Bool.true  , taut
Const→Const' (right contr) = Bool.false , contr

Const'→Const : ∀ {p} → Const' p → Const p
Const'→Const (Bool.true  , taut ) = left  taut
Const'→Const (Bool.false , contr) = right contr

Nonconst : Prop F → Set
Nonconst p = Satisfiable p × Falsifiable p

Nonconst' : Prop F → Set
Nonconst' p = never (Const p)

Nonconst→Nonconst' : ∀ {p} → Nonconst p → Nonconst' p
Nonconst→Nonconst' {p} (_ , (a , a-makes-false)) (left taut)   = NonContradiction' p a (taut a) a-makes-false
Nonconst→Nonconst' {p} ((a , a-makes-true) , _)  (right contr) = NonContradiction' p a a-makes-true (contr a)

sat-∧ˡ : ∀ p q
  → Tautology p
  → Satisfiable q
  → Satisfiable (p ∧ q)
sat-∧ˡ p q taut-p (a , sat) = a , (
  eval (p ∧ q) a            ≡⟨⟩
  eval p a  Bool.∧ eval q a ≡⟨ cong (Bool._∧ eval q a) (taut-p a) ⟩
  Bool.true Bool.∧ eval q a ≡⟨⟩
  eval q a                  ≡⟨ sat ⟩
  Bool.true                 ∎)

sat-∧ʳ : ∀ p q
  → Tautology q
  → Satisfiable p
  → Satisfiable (p ∧ q)
sat-∧ʳ p q taut-q (a , sat) = a , (
  eval (p ∧ q) a            ≡⟨⟩
  eval p a Bool.∧ eval q a  ≡⟨ cong (eval p a Bool.∧_) (taut-q a) ⟩
  eval p a Bool.∧ Bool.true ≡⟨ cong (Bool._∧ Bool.true) sat ⟩
  Bool.true                 ∎)

fal-∧ : ∀ p q
  → Falsifiable q
  → Falsifiable (p ∧ q)
fal-∧ p q (a , unsat) = a , (
  eval (p ∧ q) a             ≡⟨⟩
  eval p a Bool.∧ eval q a   ≡⟨ cong (eval p a Bool.∧_) unsat ⟩
  eval p a Bool.∧ Bool.false ≡⟨ ∧-zeroʳ (eval p a) ⟩
  Bool.false                 ∎)

-- generalize?
fal-∧-cong : ∀ p q
  → Falsifiable (p ∧ q)
  → Falsifiable (q ∧ p)
fal-∧-cong p q (a , unsat) rewrite ∧-comm (eval p a) (eval q a) = a , unsat

taut-∧ : ∀ p q
  → Tautology p
  → Tautology q
  → Tautology (p ∧ q)
taut-∧ p q taut-p taut-q a rewrite taut-p a | taut-q a = refl

contr-∧ˡ : ∀ p q
  → Contradiction p
  → Contradiction (p ∧ q)
contr-∧ˡ p q contr-p a rewrite contr-p a = refl

contr-∧ʳ : ∀ p q
  → Contradiction q
  → Contradiction (p ∧ q)
contr-∧ʳ p q contr-q a =
    eval (p ∧ q) a             ≡⟨⟩
    eval p a Bool.∧ eval q a   ≡⟨ cong (eval p a Bool.∧_) (contr-q a) ⟩
    eval p a Bool.∧ Bool.false ≡⟨ ∧-comm (eval p a) Bool.false ⟩
    Bool.false                 ∎

