module Vatras.Framework.Relation.SyntaxTest where

open import Vatras.Framework.Definitions
open import Vatras.Lang.All
open import Vatras.Translation.LanguageMap
open import Size using (Size; ∞)
open import Data.Nat using (ℕ; _+_; _≤_; suc; z≤n; s≤s)
open import Data.List using (sum)

open import Vatras.Framework.Variants using (Rose; _-<_>-)
open import Vatras.Framework.Relation.Syntax (Rose ∞)

open 2CC using (2CC; 2CCL; _⟨_,_⟩; _-<_>-)
open ADT using (ADT; ADTL; _⟨_,_⟩; leaf)

RADT  = ADT (Rose ∞)
RADTL = ADTL (Rose ∞)

count-atoms-2CC : ∀ {F i A} → 2CC F i A → ℕ
count-atoms-2CC (a -< cs >-)  = 1 + sum (Data.List.map count-atoms-2CC cs)
count-atoms-2CC (D ⟨ l , r ⟩) = count-atoms-2CC l + count-atoms-2CC r

count-atoms-Rose : ∀ {i A} → Rose i A → ℕ
count-atoms-Rose (a -< cs >-) = 1 + sum (Data.List.map count-atoms-Rose cs)

count-atoms-ADT : ∀ {i A} → RADT i A → ℕ
count-atoms-ADT (leaf v)      = count-atoms-Rose v
count-atoms-ADT (D ⟨ l , r ⟩) = count-atoms-ADT l + count-atoms-ADT r

2CCML : ∀ (F : 𝔽) → MeasurableVariabilityLanguage (Rose ∞)
2CCML F = [ 2CCL F , count-atoms-2CC ]

ADTML : ∀ (F : 𝔽) → MeasurableVariabilityLanguage (Rose ∞)
ADTML F = [ RADTL F , count-atoms-ADT ]

open import Data.Product using (_,_)
open import Data.Empty using (⊥-elim)
open import Vatras.Framework.Relation.Expression (Rose ∞)
-- open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong)

module _ (F : 𝔽) where
  p : ∀ {A : 𝔸} (l : 2CC F ∞ A) (m : RADT F A)
    → 2CCL F , RADTL F ⊢ l ≣ m
    → count-atoms-2CC l ≤ count-atoms-ADT m
  p (a -< cs >-) (leaf (b -< cs' >-)) (sub , sup) = s≤s {!!} -- use induction hypothesis on children lists
  p (a -< cs >-) (D ⟨ l , r ⟩) x = {!!} -- x is violated
  p (D ⟨ l , r ⟩) m x = {!!}

  proof : 2CCML F ⊵ ADTML F
  proof = p
