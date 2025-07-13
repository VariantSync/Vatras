open import Vatras.Framework.Definitions using (𝔸; 𝔽; atomsEqual?)
open import Relation.Binary.Definitions using (DecidableEquality)

module Vatras.Translation.Lang.2CC.Idempotence (Dimension : 𝔽) (_==_ : DecidableEquality Dimension) where

import Data.List as List
import Data.List.Properties as List
open import Data.Bool using (true; false; if_then_else_)
import Data.Bool.Properties as Bool
open import Data.Product using (_,_)
open import Function using (id)
open import Size using (Size; ∞)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality as Eq using (refl; _≗_)
open Eq.≡-Reasoning

open import Vatras.Data.EqIndexedSet using (≗→≅[]; ≅[]-sym)
open import Vatras.Framework.Compiler using (LanguageCompiler)
open import Vatras.Framework.Variants as V using (Rose)
open import Vatras.Lang.All
open 2CC

_≟_ : ∀ {i : Size} {A : 𝔸} → DecidableEquality (2CC Dimension i A)
_≟_ {A = A} (a₁ -< cs₁ >-) (a₂ -< cs₂ >-) with atomsEqual? A a₁ a₂ | List.≡-dec _≟_ cs₁ cs₂
(a₁ -< cs₁ >-) ≟ (a₂ -< cs₂ >-) | yes a₁≡a₂ | yes cs₁≡cs₂ = yes (Eq.cong₂ _-<_>- a₁≡a₂ cs₁≡cs₂)
(a₁ -< cs₁ >-) ≟ (a₂ -< cs₂ >-) | yes a₁≡a₂ | no cs₁≢cs₂ = no λ where refl → cs₁≢cs₂ refl
(a₁ -< cs₁ >-) ≟ (a₂ -< cs₂ >-) | no a₁≢a₂ | _ = no λ where refl → a₁≢a₂ refl
(a₁ -< cs₁ >-) ≟ (D₂ ⟨ l₂ , r₂ ⟩) = no λ where ()
(D₁ ⟨ l₁ , r₁ ⟩) ≟ (a₂ -< cs₂ >-) = no λ where ()
(D₁ ⟨ l₁ , r₁ ⟩) ≟ (D₂ ⟨ l₂ , r₂ ⟩) with D₁ == D₂ | l₁ ≟ l₂ | r₁ ≟ r₂
(D₁ ⟨ l₁ , r₁ ⟩) ≟ (D₂ ⟨ l₂ , r₂ ⟩) | yes D₁≡d₂ | yes l₁≡l₂ | yes r₁≡r₂ = yes (Eq.cong₂ (λ f r → f r) (Eq.cong₂ _⟨_,_⟩ D₁≡d₂ l₁≡l₂) r₁≡r₂)
(D₁ ⟨ l₁ , r₁ ⟩) ≟ (D₂ ⟨ l₂ , r₂ ⟩) | yes D₁≡d₂ | yes l₁≡l₂ | no r₁≢r₂ = no λ where refl → r₁≢r₂ refl
(D₁ ⟨ l₁ , r₁ ⟩) ≟ (D₂ ⟨ l₂ , r₂ ⟩) | yes D₁≡d₂ | no l₁≢l₂ | _ = no λ where refl → l₁≢l₂ refl
(D₁ ⟨ l₁ , r₁ ⟩) ≟ (D₂ ⟨ l₂ , r₂ ⟩) | no D₁≢d₂ | _ | _ = no λ where refl → D₁≢d₂ refl

eliminate-idempotent-choices : ∀ {i : Size} {A : 𝔸} → 2CC Dimension i A → 2CC Dimension ∞ A
eliminate-idempotent-choices (a -< cs >-) = a -< List.map eliminate-idempotent-choices cs >-
eliminate-idempotent-choices (D ⟨ l , r ⟩) with eliminate-idempotent-choices l ≟ eliminate-idempotent-choices r
eliminate-idempotent-choices (D ⟨ l , r ⟩) | yes l≡r = eliminate-idempotent-choices l
eliminate-idempotent-choices (D ⟨ l , r ⟩) | no l≢r = D ⟨ eliminate-idempotent-choices l , eliminate-idempotent-choices r ⟩

eliminate-idempotent-choices-preserves
  : ∀ {i : Size} {A : 𝔸}
  → (e : 2CC Dimension i A)
  → ⟦ eliminate-idempotent-choices e ⟧ ≗ ⟦ e ⟧
eliminate-idempotent-choices-preserves (a -< cs >-) c =
    ⟦ eliminate-idempotent-choices (a -< cs >-) ⟧ c
  ≡⟨⟩
    ⟦ a -< List.map eliminate-idempotent-choices cs >- ⟧ c
  ≡⟨⟩
    a V.-< List.map (λ e → ⟦ e ⟧ c) (List.map eliminate-idempotent-choices cs) >-
  ≡⟨ Eq.cong (a Rose.-<_>-) (List.map-∘ cs) ⟨
    a V.-< List.map (λ e → ⟦ eliminate-idempotent-choices e ⟧ c) cs >-
  ≡⟨ Eq.cong (a Rose.-<_>-) (List.map-cong (λ e → eliminate-idempotent-choices-preserves e c) cs) ⟩
    a V.-< List.map (λ e → ⟦ e ⟧ c) cs >-
  ≡⟨⟩
    ⟦ a -< cs >- ⟧ c
  ∎
eliminate-idempotent-choices-preserves (D ⟨ l , r ⟩) c with eliminate-idempotent-choices l ≟ eliminate-idempotent-choices r
eliminate-idempotent-choices-preserves (D ⟨ l , r ⟩) c | no l≢r =
    (if c D then ⟦ eliminate-idempotent-choices l ⟧ c else ⟦ eliminate-idempotent-choices r ⟧ c)
  ≡⟨ Eq.cong₂ (if c D then_else_) (eliminate-idempotent-choices-preserves l c) (eliminate-idempotent-choices-preserves r c) ⟩
    (if c D then ⟦ l ⟧ c else ⟦ r ⟧ c)
  ≡⟨⟩
    ⟦ D ⟨ l , r ⟩ ⟧ c
  ∎
eliminate-idempotent-choices-preserves (D ⟨ l , r ⟩) c | yes l≡r with c D
eliminate-idempotent-choices-preserves (D ⟨ l , r ⟩) c | yes l≡r | true =
    ⟦ eliminate-idempotent-choices l ⟧ c
  ≡⟨ eliminate-idempotent-choices-preserves l c ⟩
    ⟦ l ⟧ c
  ≡⟨⟩
    (if true then ⟦ l ⟧ c else ⟦ r ⟧ c)
  ∎
eliminate-idempotent-choices-preserves (D ⟨ l , r ⟩) c | yes l≡r | false =
    ⟦ eliminate-idempotent-choices l ⟧ c
  ≡⟨ Eq.cong₂ ⟦_⟧ l≡r refl ⟩
    ⟦ eliminate-idempotent-choices r ⟧ c
  ≡⟨ eliminate-idempotent-choices-preserves r c ⟩
    ⟦ r ⟧ c
  ≡⟨⟩
    (if false then ⟦ l ⟧ c else ⟦ r ⟧ c)
  ∎

Idempotence-Elimination : LanguageCompiler (2CCL Dimension) (2CCL Dimension)
Idempotence-Elimination = record
  { compile = eliminate-idempotent-choices
  ; config-compiler = λ _ → record { to = id ; from = id }
  ; preserves = λ e → ≅[]-sym (≗→≅[] (eliminate-idempotent-choices-preserves e))
  }
