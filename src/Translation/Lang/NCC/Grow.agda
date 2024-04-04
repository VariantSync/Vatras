{-# OPTIONS --sized-types #-}

open import Framework.Definitions using (𝕍; atoms)
open import Framework.Construct using (_∈ₛ_; cons)
open import Construct.Artifact as At using () renaming (Syntax to Artifact; _-<_>- to artifact-constructor)

{-
This module defines a compiler from NCC to NCC where the number N of alternatives per
choice grows. The compiler duplicates the last alternative in each choice to grow the vector
of alternatives to match a desired larger size.
-}
module Translation.Lang.NCC.Grow (Variant : 𝕍) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

open import Data.Empty using (⊥-elim)
import Data.EqIndexedSet as IndexedSet
open import Data.Fin as Fin using (Fin; zero; suc)
import Data.Fin.Properties as Fin
open import Data.List as List using (List; []; _∷_)
import Data.List.Properties as List
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n; _+_; _∸_)
open import Data.Nat.Properties as ℕ using (≤-refl; ≤-reflexive; ≤-trans; <-trans)
open import Data.Product using (_×_; _,_)
open import Data.Vec as Vec using (Vec; []; _∷_)
import Data.Vec.Properties as Vec
open import Framework.Compiler using (LanguageCompiler; _⊕_)
open import Framework.Definitions using (𝔸; 𝔽)
open import Framework.Relation.Function using (from; to)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; _≗_)
open import Relation.Nullary.Decidable using (yes; no)
open import Size using (Size; ∞)
import Util.AuxProofs as ℕ
open import Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs)
import Util.Vec as Vec

open Eq.≡-Reasoning using (step-≡; step-≡˘; _≡⟨⟩_; _∎)
open IndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-sym)

open import Lang.All.Generic Variant Artifact∈ₛVariant
open NCC using (NCC; NCCL; _-<_>-; _⟨_⟩)

artifact : {A : 𝔸} → atoms A → List (Variant A) → Variant A
artifact a cs = cons Artifact∈ₛVariant (artifact-constructor a cs)

-- Increasing the arity is straightforward. We have to duplicate one element (we choose the last one to be consistent with the saturation semantic of `CCC`, see `find-or-last`) until the arity difference is zero.
-- For symmetry, this module provides a translation from the 2-ary `NCC`, because, for simplicity of the proof, ShrinkTo2 translates to the 2-ary `NCC`.
-- However, the proof of the generalizaton is almost identical so we prove the generalization directly and then specialize the proof.
grow : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
  → (n m : ℕ≥ 2)
  → n ℕ≥.≤ m
  → NCC n D i A
  → NCC m D i A
grow n m n≤m (a -< cs >-) = a -< List.map (grow n m n≤m) cs >-
grow (sucs n) m n≤m (d ⟨ cs ⟩) = d ⟨ Vec.saturate n≤m (Vec.map (grow (sucs n) m n≤m) cs) ⟩

conf : ∀ {D : 𝔽}
  → (n m : ℕ≥ 2)
  → n ℕ≥.≤ m
  → NCC.Configuration n D
  → NCC.Configuration m D
conf (sucs n) (sucs m) n≤m config d = Fin.inject≤ (config d) n≤m

fnoc : ∀ {D : 𝔽}
  → (n m : ℕ≥ 2)
  → n ℕ≥.≤ m
  → NCC.Configuration m D
  → NCC.Configuration n D
fnoc (sucs n) (sucs m) n≤m config d = ℕ≥.cappedFin (Fin.toℕ (config d))

preserves-⊆ : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
  → (n m : ℕ≥ 2)
  → (n≤m : n ℕ≥.≤ m)
  → (expr : NCC n D i A)
  → NCC.⟦ grow n m n≤m expr ⟧ ⊆[ fnoc n m n≤m ] NCC.⟦ expr ⟧
preserves-⊆ n m n≤m (a -< cs >-) config =
    NCC.⟦ grow n m n≤m (a -< cs >-) ⟧ config
  ≡⟨⟩
    NCC.⟦ a -< List.map (grow n m n≤m) cs >- ⟧ config
  ≡⟨⟩
    artifact a (List.map (λ e → NCC.⟦ e ⟧ config) (List.map (grow n m n≤m) cs))
  ≡˘⟨ Eq.cong₂ artifact Eq.refl (List.map-∘ cs) ⟩
    artifact a (List.map (λ e → NCC.⟦ grow n m n≤m e ⟧ config) cs)
  ≡⟨ Eq.cong₂ artifact Eq.refl (List.map-cong (λ e → preserves-⊆ n m n≤m e config) cs) ⟩
    artifact a (List.map (λ e → NCC.⟦ e ⟧ (fnoc n m n≤m config)) cs)
  ≡⟨⟩
    NCC.⟦ a -< cs >- ⟧ (fnoc n m n≤m config)
  ∎
preserves-⊆ (sucs n) (sucs m) n≤m (d ⟨ cs ⟩) config =
    NCC.⟦ grow (sucs n) (sucs m) n≤m (d ⟨ cs ⟩) ⟧ config
  ≡⟨⟩
    NCC.⟦ d ⟨ Vec.saturate n≤m (Vec.map (grow (sucs n) (sucs m) n≤m) cs) ⟩ ⟧ config
  ≡⟨⟩
    NCC.⟦ Vec.lookup (Vec.saturate n≤m (Vec.map (grow (sucs n) (sucs m) n≤m) cs)) (config d) ⟧ config
  ≡⟨ Eq.cong₂ NCC.⟦_⟧ (Eq.cong₂ Vec.lookup (Vec.saturate-map n≤m (grow (sucs n) (sucs m) n≤m) cs) refl) refl ⟩
    NCC.⟦ Vec.lookup (Vec.map (grow (sucs n) (sucs m) n≤m) (Vec.saturate n≤m cs)) (config d) ⟧ config
  ≡⟨ Eq.cong₂ NCC.⟦_⟧ (Vec.lookup-map (config d) (grow (sucs n) (sucs m) n≤m) (Vec.saturate n≤m cs)) refl ⟩
    NCC.⟦ (grow (sucs n) (sucs m) n≤m) (Vec.lookup (Vec.saturate n≤m cs) (config d)) ⟧ config
  ≡⟨ preserves-⊆ (sucs n) (sucs m) n≤m (Vec.lookup (Vec.saturate n≤m cs) (config d)) config ⟩
    NCC.⟦ Vec.lookup (Vec.saturate n≤m cs) (config d) ⟧ (fnoc (sucs n) (sucs m) n≤m config)
  ≡⟨ Eq.cong₂ NCC.⟦_⟧ (Vec.lookup-saturate n≤m cs (config d)) refl ⟩
    NCC.⟦ Vec.lookup cs (fnoc (sucs n) (sucs m) n≤m config d) ⟧ (fnoc (sucs n) (sucs m) n≤m config)
  ≡⟨⟩
    NCC.⟦ d ⟨ cs ⟩ ⟧ (fnoc (sucs n) (sucs m) n≤m config)
  ∎

preserves-⊇ : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
  → (n m : ℕ≥ 2)
  → (n≤m : n ℕ≥.≤ m)
  → (expr : NCC n D i A)
  → NCC.⟦ expr ⟧ ⊆[ conf n m n≤m ] NCC.⟦ grow n m n≤m expr ⟧
preserves-⊇ n m n≤m (a -< cs >-) config =
    artifact a (List.map (λ e → NCC.⟦ e ⟧ config) cs)
  ≡⟨ Eq.cong₂ artifact Eq.refl (List.map-cong (λ e → preserves-⊇ n m n≤m e config) cs) ⟩
    artifact a (List.map (λ e → NCC.⟦ grow n m n≤m e ⟧ (conf n m n≤m config)) cs)
  ≡⟨ Eq.cong₂ artifact Eq.refl (List.map-∘ cs) ⟩
    NCC.⟦ a -< List.map (grow n m n≤m) cs >- ⟧ (conf n m n≤m config)
  ≡⟨⟩
    artifact a (List.map (λ e → NCC.⟦ e ⟧ (conf n m n≤m config)) (List.map (grow n m n≤m) cs))
  ∎
preserves-⊇ (sucs n) (sucs m) n≤m (d ⟨ cs ⟩) config =
    NCC.⟦ d ⟨ cs ⟩ ⟧ config
  ≡⟨⟩
    NCC.⟦ Vec.lookup cs (config d) ⟧ config
  ≡˘⟨ Eq.cong₂ NCC.⟦_⟧ (Eq.cong₂ Vec.lookup (refl {x = cs}) (ℕ≥.cappedFin-toℕ (config d))) refl ⟩
    NCC.⟦ Vec.lookup cs (ℕ≥.cappedFin (Fin.toℕ (config d))) ⟧ config
  ≡˘⟨ Eq.cong₂ NCC.⟦_⟧ (Eq.cong₂ Vec.lookup (refl {x = cs}) (Eq.cong ℕ≥.cappedFin (Fin.toℕ-inject≤ (config d) n≤m))) refl ⟩
    NCC.⟦ Vec.lookup cs (ℕ≥.cappedFin (Fin.toℕ (Fin.inject≤ (config d) n≤m))) ⟧ config
  ≡˘⟨ Eq.cong₂ NCC.⟦_⟧ (Vec.lookup-saturate n≤m cs (Fin.inject≤ (config d) n≤m)) refl ⟩
    NCC.⟦ Vec.lookup (Vec.saturate n≤m cs) (Fin.inject≤ (config d) n≤m) ⟧ config
  ≡⟨⟩
    NCC.⟦ Vec.lookup (Vec.saturate n≤m cs) (conf (sucs n) (sucs m) n≤m config d) ⟧ config
  ≡⟨ preserves-⊇ (sucs n) (sucs m) n≤m (Vec.lookup (Vec.saturate n≤m cs) (conf (sucs n) (sucs m) n≤m config d)) config ⟩
    NCC.⟦ (grow (sucs n) (sucs m) n≤m) (Vec.lookup (Vec.saturate n≤m cs) (conf (sucs n) (sucs m) n≤m config d)) ⟧ (conf (sucs n) (sucs m) n≤m config)
  ≡˘⟨ Eq.cong₂ NCC.⟦_⟧ (Vec.lookup-map (conf (sucs n) (sucs m) n≤m config d) (grow (sucs n) (sucs m) n≤m) (Vec.saturate n≤m cs)) refl ⟩
    NCC.⟦ Vec.lookup (Vec.map (grow (sucs n) (sucs m) n≤m) (Vec.saturate n≤m cs)) (conf (sucs n) (sucs m) n≤m config d) ⟧ (conf (sucs n) (sucs m) n≤m config)
  ≡˘⟨ Eq.cong₂ NCC.⟦_⟧ (Eq.cong₂ Vec.lookup (Vec.saturate-map n≤m (grow (sucs n) (sucs m) n≤m) cs) refl) refl ⟩
    NCC.⟦ Vec.lookup (Vec.saturate n≤m (Vec.map (grow (sucs n) (sucs m) n≤m) cs)) (conf (sucs n) (sucs m) n≤m config d) ⟧ (conf (sucs n) (sucs m) n≤m config)
  ≡⟨⟩
    NCC.⟦ d ⟨ Vec.saturate n≤m (Vec.map (grow (sucs n) (sucs m) n≤m) cs) ⟩ ⟧ (conf (sucs n) (sucs m) n≤m config)
  ≡⟨⟩
    NCC.⟦ grow (sucs n) (sucs m) n≤m (d ⟨ cs ⟩) ⟧ (conf (sucs n) (sucs m) n≤m config)
  ∎

preserves : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
  → (n m : ℕ≥ 2)
  → (n≤m : n ℕ≥.≤ m)
  → (expr : NCC n D i A)
  → NCC.⟦ grow n m n≤m expr ⟧ ≅[ fnoc n m n≤m ][ conf n m n≤m ] NCC.⟦ expr ⟧
preserves n m n≤m expr = preserves-⊆ n m n≤m expr , preserves-⊇ n m n≤m expr

growCompiler : ∀ {i : Size} {D : 𝔽}
  → (n m : ℕ≥ 2)
  → n ℕ≥.≤ m
  → LanguageCompiler (NCCL {i} n D) (NCCL {i} m D)
growCompiler n m n≤m .LanguageCompiler.compile = grow n m n≤m
growCompiler n m n≤m .LanguageCompiler.config-compiler expr .to = conf n m n≤m
growCompiler n m n≤m .LanguageCompiler.config-compiler expr .from = fnoc n m n≤m
growCompiler n m n≤m .LanguageCompiler.preserves expr = ≅[]-sym (preserves n m n≤m expr)

growFrom2Compiler : ∀ {i : Size} {D : 𝔽} → (n : ℕ≥ 2) → LanguageCompiler (NCCL {i} (sucs zero) D) (NCCL {i} n D)
growFrom2Compiler (sucs n) = growCompiler (sucs zero) (sucs n) (ℕ≥.lift≤ z≤n)
