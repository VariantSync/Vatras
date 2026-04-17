open import Vatras.Framework.Definitions using (𝔽; 𝔸; atoms)

module Vatras.Translation.Lang.OC-to-PropOC (F : 𝔽) where

open import Data.Bool using (if_then_else_)
open import Data.List as List using (List)
import Data.List.Properties as List
open import Data.Maybe using (nothing; just)
open import Function using (flip; id)
open import Size using (Size; ∞)
open import Relation.Binary.PropositionalEquality as Eq using (_≗_)

open import Vatras.Data.EqIndexedSet using (_≅[_][_]_; ≗→≅[]; ≅[]-sym)
open import Vatras.Data.Prop using (var)
open import Vatras.Framework.Compiler using (LanguageCompiler)
open import Vatras.Framework.Relation.Function using (from; to)
open import Vatras.Framework.Variants as V using (Rose)
open import Vatras.Framework.Relation.Expressiveness (Rose ∞) using (expressiveness-from-compiler; _≽_)
open import Vatras.Lang.All
open OC using (OC; WFOC; WFOCL; Root; _-<_>-; _❲_❳)
open PropOC using (PropOC; WFPropOC; WFPropOCL)

translate' : ∀ {i : Size} {A : 𝔸} → OC F i A → PropOC F i A
translate' (a -< cs >-) = a -< List.map translate' cs >-
translate' (f ❲ c ❳) = var f ❲ translate' c ❳

translate : ∀ {i : Size} {A : 𝔸} → WFOC F i A → WFPropOC F i A
translate (Root a cs) = Root a (List.map translate' cs)

translate'-preserves-≗
  : ∀ {i : Size} {A : 𝔸}
  → (e : OC F i A)
  → PropOC.⟦ translate' e ⟧ₒ ≗ OC.⟦ e ⟧ₒ

translate'-preserves-≗-recurse : ∀ {i : Size} {A : 𝔸}
  → (cs : List (OC F i A))
  → PropOC.⟦ List.map translate' cs ⟧ₒ-recurse ≗ OC.⟦ cs ⟧ₒ-recurse

translate'-preserves-≗ (a -< cs >-) assignment = Eq.cong (λ x → just (a V.-< x >-)) (translate'-preserves-≗-recurse cs assignment)
translate'-preserves-≗ (f ❲ c ❳) assignment = Eq.cong (if assignment f then_else nothing) (translate'-preserves-≗ c assignment)

translate'-preserves-≗-recurse cs assignment =
  begin
    PropOC.⟦ List.map translate' cs ⟧ₒ-recurse assignment
  ≡⟨⟩
    List.catMaybes (List.map (flip PropOC.⟦_⟧ₒ assignment) (List.map translate' cs))
  ≡⟨ Eq.cong List.catMaybes (List.map-∘ cs) ⟨
    List.catMaybes (List.map (λ e → PropOC.⟦ translate' e ⟧ₒ assignment) cs)
  ≡⟨ Eq.cong List.catMaybes (List.map-cong (flip translate'-preserves-≗ assignment) cs) ⟩
    List.catMaybes (List.map (flip OC.⟦_⟧ₒ assignment) cs)
  ≡⟨⟩
    OC.⟦ cs ⟧ₒ-recurse assignment
  ∎
  where
  open Eq.≡-Reasoning

translate-preserves-≗
  : ∀ {i : Size} {A : 𝔸}
  → (e : WFOC F i A)
  → PropOC.⟦ translate e ⟧ ≗ OC.⟦ e ⟧
translate-preserves-≗ (Root a cs) assignment = Eq.cong (a V.-<_>-) (translate'-preserves-≗-recurse cs assignment)

translate-preserves
  : ∀ {i : Size} {A : 𝔸}
  → (e : WFOC F i A)
  → PropOC.⟦ translate e ⟧ ≅[ id ][ id ] OC.⟦ e ⟧
translate-preserves e = ≗→≅[] (translate-preserves-≗ e)

OC→PropOC : LanguageCompiler (WFOCL F) (WFPropOCL F)
OC→PropOC .LanguageCompiler.compile = translate
OC→PropOC .LanguageCompiler.config-compiler e .to = id
OC→PropOC .LanguageCompiler.config-compiler e .from = id
OC→PropOC .LanguageCompiler.preserves e = ≅[]-sym (translate-preserves e)

PropOC≽OC : WFPropOCL F ≽ WFOCL F
PropOC≽OC = expressiveness-from-compiler OC→PropOC
