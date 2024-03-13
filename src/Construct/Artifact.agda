module Construct.Artifact where

open import Data.List using (List; map)
open import Data.List.Properties using (map-cong; map-∘)
open import Data.Product using (proj₁; proj₂; _,_)
open import Level using (_⊔_)
open import Function using (id; flip; _$_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Framework.Definitions
open import Framework.VariabilityLanguage
open import Framework.Construct
open import Framework.Compiler using (LanguageCompiler)
open LanguageCompiler
import Data.IndexedSet

open import Construct.Plain.Artifact public

Syntax : ℂ
Syntax E A = Artifact A (E A)

Construct : PlainConstruct
Construct = Plain-⟪ Syntax , (λ Γ e c → map-children (flip (Semantics Γ) c) e) ⟫
