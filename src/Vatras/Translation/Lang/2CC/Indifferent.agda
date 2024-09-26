open import Vatras.Framework.Definitions using (𝔸; 𝔽)
open import Relation.Binary.Definitions using (DecidableEquality)

module Vatras.Translation.Lang.2CC.Indifferent (Dimension : 𝔽) (_==_ : DecidableEquality Dimension) where

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
open import Vatras.Lang.2CC

_≟_ : ∀ {i : Size} {A : 𝔸} → DecidableEquality (2CC Dimension i A)
_≟_ {A = _ , _≟ₐ_} (a₁ -< cs₁ >-) (a₂ -< cs₂ >-) with a₁ ≟ₐ a₂ | List.≡-dec _≟_ cs₁ cs₂
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

eliminate-indifferent : ∀ {i : Size} {A : 𝔸} → 2CC Dimension i A → 2CC Dimension ∞ A
eliminate-indifferent (a -< cs >-) = a -< List.map eliminate-indifferent cs >-
eliminate-indifferent (D ⟨ l , r ⟩) with eliminate-indifferent l ≟ eliminate-indifferent r
eliminate-indifferent (D ⟨ l , r ⟩) | yes l≡r = eliminate-indifferent l
eliminate-indifferent (D ⟨ l , r ⟩) | no l≢r = D ⟨ eliminate-indifferent l , eliminate-indifferent r ⟩

eliminate-indifferent-preserves
  : ∀ {i : Size} {A : 𝔸}
  → (e : 2CC Dimension i A)
  → ⟦ eliminate-indifferent e ⟧ ≗ ⟦ e ⟧
eliminate-indifferent-preserves (a -< cs >-) c =
    ⟦ eliminate-indifferent (a -< cs >-) ⟧ c
  ≡⟨⟩
    ⟦ a -< List.map eliminate-indifferent cs >- ⟧ c
  ≡⟨⟩
    a V.-< List.map (λ e → ⟦ e ⟧ c) (List.map eliminate-indifferent cs) >-
  ≡⟨ Eq.cong (a Rose.-<_>-) (List.map-∘ cs) ⟨
    a V.-< List.map (λ e → ⟦ eliminate-indifferent e ⟧ c) cs >-
  ≡⟨ Eq.cong (a Rose.-<_>-) (List.map-cong (λ e → eliminate-indifferent-preserves e c) cs) ⟩
    a V.-< List.map (λ e → ⟦ e ⟧ c) cs >-
  ≡⟨⟩
    ⟦ a -< cs >- ⟧ c
  ∎
eliminate-indifferent-preserves (D ⟨ l , r ⟩) c with eliminate-indifferent l ≟ eliminate-indifferent r
eliminate-indifferent-preserves (D ⟨ l , r ⟩) c | no l≢r =
    (if c D then ⟦ eliminate-indifferent l ⟧ c else ⟦ eliminate-indifferent r ⟧ c)
  ≡⟨ Eq.cong₂ (if c D then_else_) (eliminate-indifferent-preserves l c) (eliminate-indifferent-preserves r c) ⟩
    (if c D then ⟦ l ⟧ c else ⟦ r ⟧ c)
  ≡⟨⟩
    ⟦ D ⟨ l , r ⟩ ⟧ c
  ∎
eliminate-indifferent-preserves (D ⟨ l , r ⟩) c | yes l≡r with c D
eliminate-indifferent-preserves (D ⟨ l , r ⟩) c | yes l≡r | true =
    ⟦ eliminate-indifferent l ⟧ c
  ≡⟨ eliminate-indifferent-preserves l c ⟩
    ⟦ l ⟧ c
  ≡⟨⟩
    (if true then ⟦ l ⟧ c else ⟦ r ⟧ c)
  ∎
eliminate-indifferent-preserves (D ⟨ l , r ⟩) c | yes l≡r | false =
    ⟦ eliminate-indifferent l ⟧ c
  ≡⟨ Eq.cong₂ ⟦_⟧ l≡r refl ⟩
    ⟦ eliminate-indifferent r ⟧ c
  ≡⟨ eliminate-indifferent-preserves r c ⟩
    ⟦ r ⟧ c
  ≡⟨⟩
    (if false then ⟦ l ⟧ c else ⟦ r ⟧ c)
  ∎

Indifferent-Elimination : LanguageCompiler (2CCL Dimension) (2CCL Dimension)
Indifferent-Elimination = record
  { compile = eliminate-indifferent
  ; config-compiler = λ _ → record { to = id ; from = id }
  ; preserves = λ e → ≅[]-sym (≗→≅[] (eliminate-indifferent-preserves e))
  }
