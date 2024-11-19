{-|
This module shows that `NCC`, regardless of arity, is a subset of `CCC` by
translating the `NCC` constructors into their, less restrictive, `CCC`
equivalent.
-}
module Vatras.Translation.Lang.NCC-to-CCC where

open import Size using (Size; ∞)
import Vatras.Data.EqIndexedSet as IndexedSet
open import Data.Fin as Fin using (Fin)
open import Data.List as List using (List; []; _∷_)
import Data.List.NonEmpty as List⁺
import Data.List.Properties as List
open import Data.Product using (_,_)
open import Data.Vec as Vec using (Vec; []; _∷_)
import Data.Vec.Properties as Vec
open import Vatras.Framework.Compiler using (LanguageCompiler)
open import Vatras.Framework.Definitions using (𝔸; 𝔽)
open import Vatras.Framework.Variants as V using (Rose)
open import Vatras.Framework.Relation.Expressiveness (Rose ∞) using (expressiveness-from-compiler; _≽_)
open import Vatras.Framework.Relation.Function using (from; to)
open import Relation.Binary.PropositionalEquality as Eq using (refl)
open import Vatras.Util.List using (find-or-last; lookup⇒find-or-last)
open import Vatras.Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs)

open Eq.≡-Reasoning using (step-≡-⟨; step-≡-⟩; step-≡-∣; _∎)
open IndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-sym)

open import Vatras.Lang.All
open CCC using (CCC; CCCL; _-<_>-; _⟨_⟩)
open NCC using (NCC; NCCL; _-<_>-; _⟨_⟩)

translate : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
  → (n : ℕ≥ 2)
  → NCC n D i A
  → CCC D ∞ A
translate n (a -< cs >-) = a -< List.map (translate n) cs >-
translate (sucs n) (d ⟨ c ∷ cs ⟩) = d ⟨ List⁺.fromVec (Vec.map (translate (sucs n)) (c ∷ cs)) ⟩

conf : ∀ {D : 𝔽}
  → (n : ℕ≥ 2)
  → NCC.Configuration n D
  → CCC.Configuration D
conf (sucs n) config d = Fin.toℕ (config d)

fnoc : ∀ {D : 𝔽}
  → (n : ℕ≥ 2)
  → CCC.Configuration D
  → NCC.Configuration n D
fnoc (sucs n) config d = ℕ≥.cappedFin (config d)


preserves-⊆ : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
  → (n : ℕ≥ 2)
  → (expr : NCC n D i A)
  → CCC.⟦ translate n expr ⟧ ⊆[ fnoc n ] NCC.⟦ expr ⟧
preserves-⊆ n (a -< cs >-) config =
    CCC.⟦ translate n (a -< cs >-) ⟧ config
  ≡⟨⟩
    CCC.⟦ a -< List.map (translate n) cs >- ⟧ config
  ≡⟨⟩
    a V.-< List.map (λ e → CCC.⟦ e ⟧ config) (List.map (translate n) cs) >-
  ≡⟨ Eq.cong₂ V._-<_>- refl (List.map-∘ {g = (λ e → CCC.⟦ e ⟧ config)} {f = translate n} cs) ⟨
    a V.-< List.map (λ e → CCC.⟦ translate n e ⟧ config) cs >-
  ≡⟨ Eq.cong₂ V._-<_>- refl (List.map-cong (λ e → preserves-⊆ n e config) cs) ⟩
    a V.-< List.map (λ e → NCC.⟦ e ⟧ (fnoc n config)) cs >-
  ≡⟨⟩
    NCC.⟦ a -< cs >- ⟧ (fnoc n config)
  ∎
preserves-⊆ (sucs n) (d ⟨ c ∷ cs ⟩) config =
    CCC.⟦ translate (sucs n) (d ⟨ c ∷ cs ⟩) ⟧ config
  ≡⟨⟩
    CCC.⟦ d ⟨ List⁺.fromVec (Vec.map (translate (sucs n)) (c ∷ cs)) ⟩ ⟧ config
  ≡⟨⟩
    CCC.⟦ find-or-last (config d) (List⁺.fromVec (Vec.map (translate (sucs n)) (c ∷ cs))) ⟧ config
  ≡⟨ Eq.cong₂ CCC.⟦_⟧ (lookup⇒find-or-last {m = config d} (translate (sucs n) c ∷ Vec.map (translate (sucs n)) cs)) refl ⟨
    CCC.⟦ Vec.lookup (Vec.map (translate (sucs n)) (c ∷ cs)) (ℕ≥.cappedFin (config d)) ⟧ config
  ≡⟨ Eq.cong₂ CCC.⟦_⟧ (Vec.lookup-map (ℕ≥.cappedFin (config d)) (translate (sucs n)) (c ∷ cs)) refl ⟩
    CCC.⟦ translate (sucs n) (Vec.lookup (c ∷ cs) (ℕ≥.cappedFin (config d))) ⟧ config
  ≡⟨ preserves-⊆ (sucs n) (Vec.lookup (c ∷ cs) (ℕ≥.cappedFin (config d))) config ⟩
    NCC.⟦ Vec.lookup (c ∷ cs) (fnoc (sucs n) config d) ⟧ (fnoc (sucs n) config)
  ≡⟨⟩
    NCC.⟦ d ⟨ c ∷ cs ⟩ ⟧ (fnoc (sucs n) config)
  ∎

preserves-⊇ : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
  → (n : ℕ≥ 2)
  → (expr : NCC n D i A)
  → NCC.⟦ expr ⟧ ⊆[ conf n ] CCC.⟦ translate n expr ⟧
preserves-⊇ n (a -< cs >-) config =
    NCC.⟦ a -< cs >- ⟧ config
  ≡⟨⟩
    a V.-< List.map (λ e → NCC.⟦ e ⟧ config) cs >-
  ≡⟨ Eq.cong₂ V._-<_>- refl (List.map-cong (λ e → preserves-⊇ n e config) cs) ⟩
    a V.-< List.map (λ e → CCC.⟦ translate n e ⟧ (conf n config)) cs >-
  ≡⟨ Eq.cong₂ V._-<_>- refl (List.map-∘ {g = (λ e → CCC.⟦ e ⟧ (conf n config))} {f = translate n} cs) ⟩
    a V.-< List.map (λ e → CCC.⟦ e ⟧ (conf n config)) (List.map (translate n) cs) >-
  ≡⟨⟩
    CCC.⟦ a -< List.map (translate n) cs >- ⟧ (conf n config)
  ≡⟨⟩
    CCC.⟦ translate n (a -< cs >-) ⟧ (conf n config)
  ∎
preserves-⊇ {D} {A} (sucs n) (d ⟨ c ∷ cs ⟩) config =
    NCC.⟦ d ⟨ c ∷ cs ⟩ ⟧ config
  ≡⟨⟩
    NCC.⟦ Vec.lookup (c ∷ cs) (config d) ⟧ config
  ≡⟨ preserves-⊇ (sucs n) (Vec.lookup (c ∷ cs) (config d)) config ⟩
    CCC.⟦ translate (sucs n) (Vec.lookup (c ∷ cs) (config d)) ⟧ (conf (sucs n) config)
  ≡⟨ Eq.cong₂ CCC.⟦_⟧ (Vec.lookup-map (config d) (translate (sucs n)) (c ∷ cs)) refl ⟨
    CCC.⟦ Vec.lookup (Vec.map (translate (sucs n)) (c ∷ cs)) (config d) ⟧ (conf (sucs n) config)
  ≡⟨ Eq.cong₂ CCC.⟦_⟧ (Eq.cong₂ Vec.lookup (refl {x = Vec.map (translate (sucs n)) (c ∷ cs)}) (ℕ≥.cappedFin-toℕ (config d))) refl ⟨
    CCC.⟦ Vec.lookup (Vec.map (translate (sucs n)) (c ∷ cs)) (ℕ≥.cappedFin (Fin.toℕ (config d))) ⟧ (conf (sucs n) config)
  ≡⟨ Eq.cong₂ CCC.⟦_⟧ (lookup⇒find-or-last {m = Fin.toℕ (config d)} (translate (sucs n) c ∷ Vec.map (translate (sucs n)) cs)) refl ⟩
    CCC.⟦ find-or-last (Fin.toℕ (config d)) (List⁺.fromVec (Vec.map (translate (sucs n)) (c ∷ cs))) ⟧ (conf (sucs n) config)
  ≡⟨⟩
    CCC.⟦ d ⟨ List⁺.fromVec (Vec.map (translate (sucs n)) (c ∷ cs)) ⟩ ⟧ (conf (sucs n) config)
  ≡⟨⟩
    CCC.⟦ translate (sucs n) (d ⟨ c ∷ cs ⟩) ⟧ (conf (sucs n) config)
  ∎

preserves : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
  → (n : ℕ≥ 2)
  → (expr : NCC n D i A)
  → CCC.⟦ translate n expr ⟧ ≅[ fnoc n ][ conf n ] NCC.⟦ expr ⟧
preserves n expr = preserves-⊆ n expr , preserves-⊇ n expr

NCC→CCC : ∀ {i : Size} {D : 𝔽} → (n : ℕ≥ 2) → LanguageCompiler (NCCL n D {i}) (CCCL D)
NCC→CCC n .LanguageCompiler.compile = translate n
NCC→CCC n .LanguageCompiler.config-compiler expr .to = conf n
NCC→CCC n .LanguageCompiler.config-compiler expr .from = fnoc n
NCC→CCC n .LanguageCompiler.preserves expr = ≅[]-sym (preserves n expr)

CCC≽NCC : {D : 𝔽} → (n : ℕ≥ 2) → CCCL D ≽ NCCL n D
CCC≽NCC n = expressiveness-from-compiler (NCC→CCC n)
