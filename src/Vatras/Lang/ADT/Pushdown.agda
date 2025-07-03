open import Vatras.Framework.Definitions using (𝔸; 𝔽; 𝕍; atoms)
open import Data.List as List using (List; []; _∷_; _ʳ++_)

{-|
This module provides a function for inserting artifacts at the top of ADTs.
This operation means that any produced variant will have the given atom at the top.
The parameter of this module is the constructor for adding an atom on top of existing variants.
-}
module Vatras.Lang.ADT.Pushdown (F : 𝔽) (V : 𝕍)
  (_-<_>- : ∀ {A} → atoms A → List (V A) → V A)
  where

open import Data.Bool using (if_then_else_)
import Data.Bool.Properties as Bool
import Data.List.Properties as List
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open Eq.≡-Reasoning using (step-≡-⟨; step-≡-⟩; step-≡-∣; _∎)
open import Size using (Size)

open import Vatras.Lang.ADT F V

push-down-artifact : ∀ {i : Size} {A : 𝔸} → atoms A → List (ADT A) → ADT A
push-down-artifact {A = A} a cs = go cs []
  module push-down-artifact-Implementation where
  go : ∀ {i : Size} → List (ADT A) → List (V A) → ADT A
  go [] vs = leaf (a -< List.reverse vs >-)
  go (leaf v ∷ cs) vs = go cs (v ∷ vs)
  go (d ⟨ c₁ , c₂ ⟩ ∷ cs) vs = d ⟨ go (c₁ ∷ cs) vs , go (c₂ ∷ cs) vs ⟩

⟦push-down-artifact⟧ : ∀ {i : Size} {A : 𝔸}
  → (a : atoms A)
  → (cs : List (ADT A))
  → (config : Configuration)
  → ⟦ push-down-artifact a cs ⟧ config ≡ a -< List.map (λ e → ⟦ e ⟧ config) cs >-
⟦push-down-artifact⟧ {A = A} a cs config = go' cs []
  where
  open push-down-artifact-Implementation

  go' : ∀ {i : Size}
    → (cs' : List (ADT A))
    → (vs : List (V A))
    → ⟦ go a cs cs' vs ⟧ config ≡ a -< vs ʳ++ List.map (λ e → ⟦ e ⟧ config) cs' >-
  go' [] vs = Eq.sym (Eq.cong₂ _-<_>- refl (Eq.trans (List.ʳ++-defn vs) (List.++-identityʳ (List.reverse vs))))
  go' (leaf v ∷ cs') vs = Eq.trans (go' cs' (v ∷ vs)) (Eq.cong₂ _-<_>- refl (List.++-ʳ++ List.[ v ] {ys = vs}))
  go' ((d ⟨ c₁ , c₂ ⟩) ∷ cs') vs =
      ⟦ d ⟨ go a cs (c₁ ∷ cs') vs , go a cs (c₂ ∷ cs') vs ⟩ ⟧ config
    ≡⟨⟩
      (if config d
        then ⟦ go a cs (c₁ ∷ cs') vs ⟧ config
        else ⟦ go a cs (c₂ ∷ cs') vs ⟧ config)
    ≡⟨ Eq.cong₂ (if config d then_else_) (go' (c₁ ∷ cs') vs) (go' (c₂ ∷ cs') vs) ⟩
      (if config d
        then a -< vs ʳ++ List.map (λ e → ⟦ e ⟧ config) (c₁ ∷ cs') >-
        else a -< vs ʳ++ List.map (λ e → ⟦ e ⟧ config) (c₂ ∷ cs') >-)
    ≡⟨ Bool.if-float (λ c → a -< vs ʳ++ List.map (λ e → ⟦ e ⟧ config) (c ∷ cs') >-) (config d) ⟨
      a -< vs ʳ++ List.map (λ e → ⟦ e ⟧ config) ((if config d then c₁ else c₂) ∷ cs') >-
    ≡⟨⟩
      a -< vs ʳ++ ⟦ if config d then c₁ else c₂ ⟧ config ∷ List.map (λ e → ⟦ e ⟧ config) cs' >-
    ≡⟨ Eq.cong₂ _-<_>- refl (Eq.cong₂ _ʳ++_ {x = vs} refl (Eq.cong₂ _∷_ (Bool.if-float (λ e → ⟦ e ⟧ config) (config d)) refl)) ⟩
      a -< vs ʳ++ (if config d then ⟦ c₁ ⟧ config else ⟦ c₂ ⟧ config) ∷ List.map (λ e → ⟦ e ⟧ config) cs' >-
    ≡⟨⟩
      a -< vs ʳ++ ⟦ d ⟨ c₁ , c₂ ⟩ ⟧ config ∷ List.map (λ e → ⟦ e ⟧ config) cs' >-
    ≡⟨⟩
      a -< vs ʳ++ List.map (λ e → ⟦ e ⟧ config) (d ⟨ c₁ , c₂ ⟩ ∷ cs') >-
    ∎
