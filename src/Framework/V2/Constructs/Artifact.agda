module Framework.V2.Constructs.Artifact where

open import Data.List using (List; map)
open import Data.List.Properties using (map-cong; map-∘)
open import Data.Product using (proj₁; proj₂; _,_)
open import Level using (_⊔_)
open import Function using (id; _$_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Framework.V2.Variant
open import Framework.V2.Definitions hiding (Semantics)
open import Framework.V2.Compiler as Comp using (LanguageCompiler; ConfigTranslation; ConstructFunctor; Stable)
open LanguageCompiler
import Data.IndexedSet

open import Framework.V2.Constructs.Plain.Artifact public

Syntax : ℂ
Syntax E A = Artifact A (E A)

Semantics : ∀ {V : 𝕍} (S : 𝕊)
  → Syntax ∈ₛ V
  → ℂ-Semantics V S Syntax
Semantics _ V-has-Artifact conf-comp (syn _ with-sem ⟦_⟧) a c
  = cons V-has-Artifact (map-children (λ e → ⟦ e ⟧ c) a)

map-children-preserves : ∀ {V : 𝕍} {S₁ S₂ : 𝕊} {Γ₁ : VariabilityLanguage V S₁} {Γ₂ : VariabilityLanguage V S₂} {A}
  → let open IVSet V A using (_≅_; _≅[_][_]_) in
  ∀ (mkArtifact : Syntax ∈ₛ V)
  → (t : LanguageCompiler Γ₁ Γ₂)
  → (at : Syntax (Expression Γ₁) A)
  → Semantics S₁ mkArtifact id Γ₁ at
      ≅[ conf t ][ fnoc t ]
    Semantics S₁ mkArtifact (fnoc t) Γ₂ (map-children (compile t) at)
map-children-preserves {V} {S₁} {S₂} {Γ₁} {Γ₂} {A} mkArtifact t (a -< cs >-) =
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
