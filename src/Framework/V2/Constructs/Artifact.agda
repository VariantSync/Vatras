module Framework.V2.Constructs.Artifact where

open import Data.List using (List; map)
open import Data.List.Properties using (map-cong; map-∘)
open import Data.Product using (proj₁; proj₂; _,_)
open import Level using (_⊔_)
open import Function using (id; flip; _$_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Framework.Variant
open import Framework.Definitions
open import Framework.VariabilityLanguage
open import Framework.Construct
open import Framework.Compiler using (LanguageCompiler)
open LanguageCompiler
import Data.IndexedSet

open import Framework.V2.Constructs.Plain.Artifact public

Syntax : ℂ
Syntax E A = Artifact A (E A)

Construct : PlainConstruct
Construct = Plain-⟪ Syntax , (λ Γ e c → map-children (flip (Semantics Γ) c) e) ⟫

map-children-preserves : ∀ {V : 𝕍} {Γ₁ Γ₂ : VariabilityLanguage V} {A}
  → let open IVSet V A using (_≅_; _≅[_][_]_) in
  ∀ (mkArtifact : Syntax ∈ₛ V)
  → (t : LanguageCompiler Γ₁ Γ₂)
  → (a : Syntax (Expression Γ₁) A)
  → PlainConstruct-Semantics Construct mkArtifact Γ₁ a
      ≅[ conf t ][ fnoc t ]
    PlainConstruct-Semantics Construct mkArtifact Γ₂ (map-children (compile t) a)
map-children-preserves {V} {Γ₁} {Γ₂} {A} mkArtifact t (a -< cs >-) =
    ≅[]-begin
      (λ c → cons mkArtifact (a -< map (λ e → ⟦ e ⟧₁ c) cs >-))
    ≅[]⟨ t-⊆ , t-⊇ ⟩
      (λ c → cons mkArtifact (a -< map (λ e → ⟦ e ⟧₂ c) (map (compile t) cs) >-))
    ≅[]-∎
    where module I = IVSet V A
          open I using (_≅[_][_]_; _⊆[_]_)
          open I.≅[]-Reasoning
          open Eq.≡-Reasoning

          ⟦_⟧₁ = VariabilityLanguage.Semantics Γ₁
          ⟦_⟧₂ = VariabilityLanguage.Semantics Γ₂

          -- TODO: The following two proofs contain quite some redundancy that can probably be abstracted.
          t-⊆ : (λ c → cons mkArtifact (a -< map (λ e → ⟦ e ⟧₁ c) cs >-))
                  ⊆[ conf t ]
                (λ z → cons mkArtifact (a -< map (λ e → ⟦ e ⟧₂ z) (map (compile t) cs) >-))
          t-⊆ i = Eq.cong (cons mkArtifact) $ Eq.cong (a -<_>-) $
            begin
              map (λ e → ⟦ e ⟧₁ i) cs
            ≡⟨ map-cong (λ e → proj₁ (preserves t e) i) cs ⟩
              map (λ e → ⟦ compile t e ⟧₂ (conf t i)) cs
            ≡⟨ map-∘ cs ⟩
              map (λ e → ⟦ e ⟧₂ (conf t i)) (map (compile t) cs)
            ∎

          t-⊇ : (λ z → cons mkArtifact (a -< map (λ e → ⟦ e ⟧₂ z) (map (compile t) cs) >-))
                  ⊆[ fnoc t ]
                (λ c → cons mkArtifact (a -< map (λ e → ⟦ e ⟧₁ c) cs >-))
          t-⊇ i = Eq.cong (cons mkArtifact) $ Eq.cong (a -<_>-) $
            begin
              map (λ e → ⟦ e ⟧₂ i) (map (compile t) cs)
            ≡˘⟨ map-∘ cs ⟩
              map (λ e → ⟦ compile t e ⟧₂ i) cs
            ≡⟨ map-cong (λ e → proj₂ (preserves t e) i) cs ⟩
              map (λ e → ⟦ e ⟧₁ (fnoc t i)) cs
            ∎
