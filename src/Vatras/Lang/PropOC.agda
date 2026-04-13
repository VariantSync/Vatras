{-|
A specialization of option calculus with propositional formulas as dimensions.
The semantics is adapted in order to evaluate the propositional formulas.
Hence, the configuration consists of an `Assignment` of variables to `Bool`.
-}
open import Vatras.Framework.Definitions using (𝔽; ℂ; 𝔼)

module Vatras.Lang.PropOC (F : 𝔽) where

open import Data.List using (List)
open import Data.Maybe using (Maybe)
open import Function using (_∘_; flip)
open import Size using (Size; ∞)

open import Vatras.Data.Prop using (Prop; Assignment; eval)
open import Vatras.Framework.Variants as V using (Rose)
open import Vatras.Framework.VariabilityLanguage using (VariabilityLanguage; ⟪_,_,_⟫; 𝔼-Semantics)
open import Vatras.Lang.OC (Prop F) as OC
  public
  using (Root; _-<_>-; _❲_❳)
  renaming
    ( OC to PropOC
    ; WFOC to WFPropOC
    )

Configuration : ℂ
Configuration = Assignment F

⟦_⟧ₒ-recurse : ∀ {i} → 𝔼-Semantics (List ∘ Rose ∞) Configuration (List ∘ PropOC i)
⟦ e ⟧ₒ-recurse c = OC.⟦ e ⟧ₒ-recurse (flip eval c)

⟦_⟧ₒ : ∀ {i : Size} → 𝔼-Semantics (Maybe ∘ Rose ∞) Configuration (PropOC i)
⟦ e ⟧ₒ c = OC.⟦ e ⟧ₒ (flip eval c)

⟦_⟧ : ∀ {i : Size} → 𝔼-Semantics (Rose ∞) Configuration (WFPropOC i)
⟦ e ⟧ c = OC.⟦ e ⟧ (flip eval c)

PropOCL : ∀ {i : Size} → VariabilityLanguage (Maybe ∘ Rose ∞)
PropOCL {i} = ⟪ PropOC i , Configuration , ⟦_⟧ₒ ⟫

WFPropOCL : {i : Size} → VariabilityLanguage (Rose ∞)
WFPropOCL {i} = ⟪ WFPropOC i , Configuration , ⟦_⟧ ⟫
