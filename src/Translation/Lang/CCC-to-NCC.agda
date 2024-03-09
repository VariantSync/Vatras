{-# OPTIONS --sized-types #-}

open import Framework.Construct using (_∈ₛ_; cons)
open import Construct.Artifact as At using () renaming (Syntax to Artifact; _-<_>- to artifact-constructor)

module Translation.Lang.CCC-to-NCC (Variant : Set → Set) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

import Data.EqIndexedSet as IndexedSet
open import Data.Fin as Fin using (Fin)
open import Data.List as List using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.Nat using (ℕ; zero; suc; _≤_; s≤s)
open import Data.Nat.Properties as ℕ using (≤-reflexive; ≤-trans)
open import Data.Product using (_×_; _,_)
open import Data.Vec as Vec using (Vec; []; _∷_)
import Data.Vec.Properties as Vec
open import Framework.Compiler using (LanguageCompiler)
open import Framework.Relation.Expressiveness Variant using (expressiveness-from-compiler; _≽_)
open import Framework.Relation.Function using (from; to)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Size using (Size; ↑_; ∞)
open import Util.List using (find-or-last; map-find-or-last; find-or-last⇒lookup)
open import Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs; _⊔_)
import Util.Vec as Vec

open Eq.≡-Reasoning using (step-≡; step-≡˘; _≡⟨⟩_; _∎)
open IndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-sym)
open IndexedSet.≅[]-Reasoning using (step-≅[]; step-≅[]˘; _≅[]⟨⟩_; _≅[]-∎)

open import Lang.CCC as CCC using (CCC; _-<_>-; _⟨_⟩)
module CCC-Sem-1 D = CCC.Sem D Variant Artifact∈ₛVariant
open CCC-Sem-1 using (CCCL)
module CCC-Sem-2 {A} = CCC.Sem A Variant Artifact∈ₛVariant
open CCC-Sem-2 using () renaming (⟦_⟧ to ⟦_⟧ₐ)

open import Lang.NCC as NCC using (NCC; _-<_>-; _⟨_⟩)
module NCC-Sem-1 n D = NCC.Sem n D Variant Artifact∈ₛVariant
open NCC-Sem-1 using (NCCL)
module NCC-Sem-2 {n} {A} = NCC.Sem n A Variant Artifact∈ₛVariant
open NCC-Sem-2 using () renaming (⟦_⟧ to ⟦_⟧ₙ)

import Translation.Lang.NCC-to-NCC
open Translation.Lang.NCC-to-NCC Variant Artifact∈ₛVariant using (NCC→NCC)
open Translation.Lang.NCC-to-NCC.map-dim Variant Artifact∈ₛVariant using (NCC-map-dim; NCCꟲ-map-dim)
module NCC-map-dim {i} {D₁} {D₂} n f f⁻¹ is-inverse = LanguageCompiler (NCC-map-dim {i} {D₁} {D₂} n f f⁻¹ is-inverse)
open Translation.Lang.NCC-to-NCC Variant Artifact∈ₛVariant using (IndexedDimension)
module NCC→NCC {i} {D} n m = LanguageCompiler (NCC→NCC {i} {D} n m)

artifact : ∀ {A : Set} → A → List (Variant A) → Variant A
artifact a cs = cons Artifact∈ₛVariant (artifact-constructor a cs)


module Exact where
  mutual
    data ListChoiceLengthLimit {D A : Set} (n : ℕ≥ 2) : {i : Size} → List (CCC D i A) → Set where
      [] : {i : Size} → ListChoiceLengthLimit n {i} []
      _∷_ : {i : Size} → {c : CCC D i A} → {cs : List (CCC D i A)} → ChoiceLengthLimit n {i} c → ListChoiceLengthLimit n {i} cs → ListChoiceLengthLimit n {i} (c ∷ cs)

    data List⁺ChoiceLengthLimit {D A : Set} (n : ℕ≥ 2) : {i : Size} → List⁺ (CCC D i A) → Set where
      _∷_ : {i : Size} → {c : CCC D i A} → {cs : List (CCC D i A)} → ChoiceLengthLimit n {i} c → ListChoiceLengthLimit n {i} cs → List⁺ChoiceLengthLimit n {i} (c ∷ cs)

    data ChoiceLengthLimit {D A : Set} (n : ℕ≥ 2) : {i : Size} → CCC D i A → Set where
      maxArtifact : {i : Size} → {a : A} → {cs : List (CCC D i A)} → ListChoiceLengthLimit n {i} cs → ChoiceLengthLimit n {↑ i} (a -< cs >-)
      maxChoice : {i : Size} → {d : D} → {cs : List⁺ (CCC D i A)} → List⁺.length cs ≤ ℕ≥.toℕ n → List⁺ChoiceLengthLimit n {i} cs → ChoiceLengthLimit n {↑ i} (d ⟨ cs ⟩)

  mutual
    ListChoiceLengthLimit-respects-≤ : ∀ {i : Size} {D A : Set} {cs : List (CCC D i A)} {n₁ n₂ : ℕ≥ 2}
      → n₁ ℕ≥.≤ n₂
      → ListChoiceLengthLimit n₁ cs
      → ListChoiceLengthLimit n₂ cs
    ListChoiceLengthLimit-respects-≤ n₁≤n₂ [] = []
    ListChoiceLengthLimit-respects-≤ n₁≤n₂ (c ∷ cs) = ChoiceLengthLimit-respects-≤ n₁≤n₂ c ∷ ListChoiceLengthLimit-respects-≤ n₁≤n₂ cs

    List⁺ChoiceLengthLimit-respects-≤ : ∀ {i : Size} {D A : Set} {cs : List⁺ (CCC D i A)} {n₁ n₂ : ℕ≥ 2}
      → n₁ ℕ≥.≤ n₂
      → List⁺ChoiceLengthLimit n₁ cs
      → List⁺ChoiceLengthLimit n₂ cs
    List⁺ChoiceLengthLimit-respects-≤ n₁≤n₂ (c ∷ cs) = ChoiceLengthLimit-respects-≤ n₁≤n₂ c ∷ ListChoiceLengthLimit-respects-≤ n₁≤n₂ cs

    ChoiceLengthLimit-respects-≤ : ∀ {i : Size} {D A : Set} {cs : CCC D i A} {n₁ n₂ : ℕ≥ 2}
      → n₁ ℕ≥.≤ n₂
      → ChoiceLengthLimit n₁ cs
      → ChoiceLengthLimit n₂ cs
    ChoiceLengthLimit-respects-≤ n₁≤n₂ (maxArtifact max-cs) = maxArtifact (ListChoiceLengthLimit-respects-≤ n₁≤n₂ max-cs)
    ChoiceLengthLimit-respects-≤ {cs = d ⟨ cs ⟩} {n₁ = n₁} {n₂ = n₂} n₁≤n₂ (maxChoice max-cs≤n max-cs) = maxChoice (≤-trans max-cs≤n n₁≤n₂) (List⁺ChoiceLengthLimit-respects-≤ n₁≤n₂ max-cs)

  -- calculcates the maximum + 2 to ensure that it is ≥ 2
  maximum : List (ℕ≥ 2) → ℕ≥ 2
  maximum [] = sucs zero
  maximum (n ∷ ns) = n ⊔ maximum ns

  maximum⁺ : List⁺ (ℕ≥ 2) → ℕ≥ 2
  maximum⁺ (n ∷ ns) = maximum (n ∷ ns)

  -- calculcates the maximum + 2 to ensure that it is ≥ 2
  maxChoiceLength : ∀ {i : Size} {D A : Set} → CCC D i A → ℕ≥ 2
  maxChoiceLength (a -< cs >-) = maximum (List.map maxChoiceLength cs)
  maxChoiceLength (d ⟨ cs ⟩) = sucs (List⁺.length cs) ⊔ maximum⁺ (List⁺.map maxChoiceLength cs)

  mutual
    maximumIsLimit : ∀ {i : Size} {D A : Set}
      → (cs : List (CCC D i A))
      → ListChoiceLengthLimit (maximum (List.map maxChoiceLength cs)) cs
    maximumIsLimit [] = []
    maximumIsLimit (c ∷ cs) = ChoiceLengthLimit-respects-≤ (ℕ≥.m≤m⊔n (maxChoiceLength c) (maximum (List.map maxChoiceLength cs))) (maxChoiceLengthIsLimit c) ∷ ListChoiceLengthLimit-respects-≤ (ℕ≥.m≤n⊔m (maxChoiceLength c) (maximum (List.map maxChoiceLength cs))) (maximumIsLimit cs)

    maximum⁺IsLimit : ∀ {i : Size} {D A : Set}
      → (cs : List⁺ (CCC D i A))
      → List⁺ChoiceLengthLimit (maximum⁺ (List⁺.map maxChoiceLength cs)) cs
    maximum⁺IsLimit (c ∷ cs) = ChoiceLengthLimit-respects-≤ (ℕ≥.m≤m⊔n (maxChoiceLength c) (maximum (List.map maxChoiceLength cs))) (maxChoiceLengthIsLimit c) ∷ ListChoiceLengthLimit-respects-≤ (ℕ≥.m≤n⊔m (maxChoiceLength c) (maximum (List.map maxChoiceLength cs))) (maximumIsLimit cs)

    maxChoiceLengthIsLimit : ∀ {i : Size} {D A : Set}
      → (expr : CCC D i A)
      → ChoiceLengthLimit (maxChoiceLength expr) expr
    maxChoiceLengthIsLimit (a -< cs >-) = maxArtifact (maximumIsLimit cs)
    maxChoiceLengthIsLimit (d ⟨ cs ⟩) = maxChoice (ℕ.m+n≤o⇒n≤o 2 (ℕ≥.m≤m⊔n (sucs (List⁺.length cs)) (maximum⁺ (List⁺.map maxChoiceLength cs)))) (List⁺ChoiceLengthLimit-respects-≤ (ℕ≥.m≤n⊔m (sucs (List⁺.length cs)) (maximum⁺ (List⁺.map maxChoiceLength cs))) (maximum⁺IsLimit cs))

  mutual
    translate : ∀ {i : Size} {D A : Set}
      → (n : ℕ≥ 2)
      → (expr : CCC D i A)
      → ChoiceLengthLimit n {i} expr
      → NCC n D i A
    translate n (a -< cs >-) (maxArtifact max-cs) = a -< zipWith n (translate n) cs max-cs >-
    translate (sucs n) (d ⟨ c ∷ cs ⟩) (maxChoice max≤n (max-c ∷ max-cs)) =
      d ⟨ Vec.saturate max≤n (translate (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs))) ⟩

    -- Can probably be generalized
    zipWith : ∀ {i : Size} {D A Result : Set}
      → (n : ℕ≥ 2)
      → ((expr : CCC D i A) → ChoiceLengthLimit n expr → Result)
      → (cs : List (CCC D i A))
      → ListChoiceLengthLimit n cs
      → List Result
    zipWith n f [] [] = []
    zipWith n f (c ∷ cs) (max-c ∷ max-cs) = f c max-c ∷ zipWith n f cs max-cs

    length-zipWith : ∀ {i : Size} {D A Result : Set}
      → (n : ℕ≥ 2)
      → {f : (expr : CCC D i A) → ChoiceLengthLimit n expr → Result}
      → (cs : List (CCC D i A))
      → (max-cs : ListChoiceLengthLimit n cs)
      → List.length (zipWith {i} n f cs max-cs) ≡ List.length cs
    length-zipWith n [] [] = refl
    length-zipWith n (c ∷ cs) (max-c ∷ max-cs) = Eq.cong suc (length-zipWith n cs max-cs)

  map∘zipWith : ∀ {i : Size} {D A Result₁ Result₂ : Set}
    → (n : ℕ≥ 2)
    → {g : Result₁ → Result₂}
    → {f : (expr : CCC D i A) → ChoiceLengthLimit n expr → Result₁}
    → (cs : List (CCC D i A))
    → (max-cs : ListChoiceLengthLimit n cs)
    → List.map g (zipWith n f cs max-cs) ≡ zipWith n (λ e max-e → g (f e max-e)) cs max-cs
  map∘zipWith n [] [] = refl
  map∘zipWith n (c ∷ cs) (max-c ∷ max-cs) = Eq.cong₂ _∷_ refl (map∘zipWith n cs max-cs)

  zipWith-cong : ∀ {i : Size} {D A Result : Set}
    → (n : ℕ≥ 2)
    → {f g : (expr : CCC D i A) → ChoiceLengthLimit n expr → Result}
    → ((e : CCC D i A) → (max-e : ChoiceLengthLimit n e) → f e max-e ≡ g e max-e)
    → (cs : List (CCC D i A))
    → (max-cs : ListChoiceLengthLimit n cs)
    → zipWith n f cs max-cs ≡ zipWith n g cs max-cs
  zipWith-cong n f≗g [] [] = refl
  zipWith-cong n f≗g (c ∷ cs) (max-c ∷ max-cs) = Eq.cong₂ _∷_ (f≗g c max-c) (zipWith-cong n f≗g cs max-cs)

  zipWith⇒map : ∀ {i : Size} {D A Result : Set}
    → (n : ℕ≥ 2)
    → (f : (expr : CCC D i A) → Result)
    → (cs : List (CCC D i A))
    → (max-cs : ListChoiceLengthLimit n cs)
    → zipWith n (λ e max-e → f e) cs max-cs ≡ List.map f cs
  zipWith⇒map n f [] [] = refl
  zipWith⇒map n f (c ∷ cs) (max-c ∷ max-cs) = Eq.cong₂ _∷_ refl (zipWith⇒map n f cs max-cs)


  conf : ∀ {D : Set} → (n : ℕ≥ 2) → CCC.Configuration D → NCC.Configuration n D
  conf (sucs n) config d = ℕ≥.cappedFin (config d)

  fnoc : ∀ {D : Set} → (n : ℕ≥ 2) → NCC.Configuration n D → CCC.Configuration D
  fnoc n config d = Fin.toℕ (config d)

  preserves-⊆ : ∀ {i : Size} {D A : Set}
    → (n : ℕ≥ 2)
    → (expr : CCC D i A)
    → (choiceLengthLimit : ChoiceLengthLimit n expr)
    → ⟦ translate n expr choiceLengthLimit ⟧ₙ ⊆[ fnoc n ] ⟦ expr ⟧ₐ
  preserves-⊆ n (a -< cs >-) (maxArtifact max-cs) config =
      ⟦ translate n (a -< cs >-) (maxArtifact max-cs) ⟧ₙ config
    ≡⟨⟩
      ⟦ a -< zipWith n (translate n) cs max-cs >- ⟧ₙ config
    ≡⟨⟩
      artifact a (List.map (λ e → ⟦ e ⟧ₙ config) (zipWith n (translate n) cs max-cs))
    ≡⟨ Eq.cong₂ artifact refl (map∘zipWith n cs max-cs) ⟩
      artifact a (zipWith n (λ e max-e → ⟦ translate n e max-e ⟧ₙ config) cs max-cs)
    ≡⟨ Eq.cong₂ artifact refl (zipWith-cong n (λ e max-e → preserves-⊆ n e max-e config) cs max-cs) ⟩
      artifact a (zipWith n (λ e max-e → ⟦ e ⟧ₐ (fnoc n config)) cs max-cs)
    ≡⟨ Eq.cong₂ artifact refl (zipWith⇒map n (λ e → ⟦ e ⟧ₐ (fnoc n config)) cs max-cs) ⟩
      artifact a (List.map (λ e → ⟦ e ⟧ₐ (fnoc n config)) cs)
    ≡⟨⟩
      ⟦ a -< cs >- ⟧ₐ (fnoc n config)
    ∎
  preserves-⊆ (sucs n) (d ⟨ c ∷ cs ⟩) (maxChoice max≤n (max-c ∷ max-cs)) config =
      ⟦ translate (sucs n) (d ⟨ c ∷ cs ⟩) (maxChoice (max≤n) (max-c ∷ max-cs)) ⟧ₙ config
    ≡⟨⟩
      ⟦ d ⟨ Vec.saturate max≤n (translate (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs))) ⟩ ⟧ₙ config
    ≡⟨⟩
      ⟦ Vec.lookup (Vec.saturate max≤n (translate (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs)))) (config d) ⟧ₙ config
    ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Vec.lookup-saturate max≤n (translate (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs))) (config d)) refl ⟩
      ⟦ Vec.lookup (translate (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs))) (ℕ≥.cappedFin (Fin.toℕ (config d))) ⟧ₙ config
    ≡⟨⟩
      ⟦ Vec.lookup (Vec.cast (Eq.cong suc (length-zipWith (sucs n) cs max-cs)) (translate (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs))) (ℕ≥.cappedFin (Fin.toℕ (config d))) ⟧ₙ config
    ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Vec.lookup-cast₁ (Eq.cong suc (length-zipWith (sucs n) cs max-cs)) (translate (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs)) (ℕ≥.cappedFin (Fin.toℕ (config d)))) refl ⟩
      ⟦ Vec.lookup (translate (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs)) (Fin.cast (Eq.sym (Eq.cong suc (length-zipWith (sucs n) cs max-cs))) (ℕ≥.cappedFin (Fin.toℕ (config d)))) ⟧ₙ config
    ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Eq.cong₂ Vec.lookup (refl {x = translate (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs)}) (ℕ≥.cast-cappedFin (Fin.toℕ (config d)) (Eq.sym (Eq.cong suc (length-zipWith (sucs n) cs max-cs))))) refl ⟩
      ⟦ Vec.lookup (translate (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs)) (ℕ≥.cappedFin (Fin.toℕ (config d))) ⟧ₙ config
    ≡˘⟨ Eq.cong₂ ⟦_⟧ₙ (find-or-last⇒lookup (translate (sucs n) c max-c) (zipWith (sucs n) (translate (sucs n)) cs max-cs)) refl ⟩
      ⟦ find-or-last (Fin.toℕ (config d)) (translate (sucs n) c max-c ∷ zipWith (sucs n) (translate (sucs n)) cs max-cs) ⟧ₙ config
    ≡⟨ map-find-or-last (λ e → ⟦ e ⟧ₙ config) (Fin.toℕ (config d)) (translate (sucs n) c max-c ∷ zipWith (sucs n) (translate (sucs n)) cs max-cs) ⟩
      find-or-last (Fin.toℕ (config d)) (⟦ translate (sucs n) c max-c ⟧ₙ config ∷ List.map (λ e → ⟦ e ⟧ₙ config) (zipWith (sucs n) (translate (sucs n)) cs max-cs))
    ≡⟨ Eq.cong₂ find-or-last refl (Eq.cong₂ _∷_ refl (map∘zipWith (sucs n) cs max-cs)) ⟩
      find-or-last (Fin.toℕ (config d)) (⟦ translate (sucs n) c max-c ⟧ₙ config ∷ zipWith (sucs n) (λ e max-e → ⟦ translate (sucs n) e max-e ⟧ₙ config) cs max-cs)
    ≡⟨ Eq.cong₂ find-or-last refl (Eq.cong₂ _∷_ (preserves-⊆ (sucs n) c max-c config) (zipWith-cong (sucs n) (λ e max-e → preserves-⊆ (sucs n) e max-e config) cs max-cs)) ⟩
      find-or-last (Fin.toℕ (config d)) (⟦ c ⟧ₐ (fnoc (sucs n) config) ∷ zipWith (sucs n) (λ e max-e → ⟦ e ⟧ₐ (fnoc (sucs n) config)) cs max-cs)
    ≡⟨ Eq.cong₂ find-or-last refl (Eq.cong₂ _∷_ refl (zipWith⇒map (sucs n) (λ e → ⟦ e ⟧ₐ (fnoc (sucs n) config)) cs max-cs)) ⟩
      find-or-last (Fin.toℕ (config d)) (⟦ c ⟧ₐ (fnoc (sucs n) config) ∷ List.map (λ e → ⟦ e ⟧ₐ (fnoc (sucs n) config)) cs)
    ≡⟨⟩
      find-or-last (Fin.toℕ (config d)) (List⁺.map (λ e → ⟦ e ⟧ₐ (fnoc (sucs n) config)) (c ∷ cs))
    ≡˘⟨ map-find-or-last (λ e → ⟦ e ⟧ₐ (fnoc (sucs n) config)) (fnoc (sucs n) config d) (c ∷ cs) ⟩
      ⟦ find-or-last (fnoc (sucs n) config d) (c ∷ cs) ⟧ₐ (fnoc (sucs n) config)
    ≡⟨⟩
      ⟦ d ⟨ c ∷ cs ⟩ ⟧ₐ (fnoc (sucs n) config)
    ∎

  preserves-⊇ : ∀ {i : Size} {D A : Set}
    → (n : ℕ≥ 2)
    → (expr : CCC D i A)
    → (choiceLengthLimit : ChoiceLengthLimit n {i} expr)
    → ⟦ expr ⟧ₐ ⊆[ conf n ] ⟦ translate n expr choiceLengthLimit ⟧ₙ
  preserves-⊇ n (a -< cs >-) (maxArtifact max-cs) config =
      ⟦ a -< cs >- ⟧ₐ config
    ≡⟨⟩
      artifact a (List.map (λ e → ⟦ e ⟧ₐ config) cs)
    ≡˘⟨ Eq.cong₂ artifact refl (zipWith⇒map n (λ e → ⟦ e ⟧ₐ config) cs max-cs) ⟩
      artifact a (zipWith n (λ e max-e → ⟦ e ⟧ₐ config) cs max-cs)
    ≡⟨ Eq.cong₂ artifact refl (zipWith-cong n (λ e max-e → preserves-⊇ n e max-e config) cs max-cs) ⟩
      artifact a (zipWith n (λ e max-e → ⟦ translate n e max-e ⟧ₙ (conf n config)) cs max-cs)
    ≡˘⟨ Eq.cong₂ artifact refl (map∘zipWith n cs max-cs) ⟩
      artifact a (List.map (λ e → ⟦ e ⟧ₙ (conf n config)) (zipWith n (translate n) cs max-cs))
    ≡⟨⟩
      ⟦ a -< zipWith n (translate n) cs max-cs >- ⟧ₙ (conf n config)
    ≡⟨⟩
      ⟦ translate n (a -< cs >-) (maxArtifact max-cs) ⟧ₙ (conf n config)
    ∎
  preserves-⊇ (sucs n) (d ⟨ c ∷ cs ⟩) (maxChoice (s≤s max≤n) (max-c ∷ max-cs)) config =
      ⟦ d ⟨ c ∷ cs ⟩ ⟧ₐ config
    ≡⟨⟩
      ⟦ find-or-last (config d) (c ∷ cs) ⟧ₐ config
    ≡⟨ map-find-or-last (λ e → ⟦ e ⟧ₐ config) (config d) (c ∷ cs) ⟩
      find-or-last (config d) (List⁺.map (λ e → ⟦ e ⟧ₐ config) (c ∷ cs))
    ≡⟨⟩
      find-or-last (config d) (⟦ c ⟧ₐ config ∷ List.map (λ e → ⟦ e ⟧ₐ config) cs)
    ≡˘⟨ Eq.cong₂ find-or-last refl (Eq.cong₂ _∷_ refl (zipWith⇒map (sucs n) (λ e → ⟦ e ⟧ₐ config) cs max-cs)) ⟩
      find-or-last (config d) (⟦ c ⟧ₐ config ∷ zipWith (sucs n) (λ e max-e → ⟦ e ⟧ₐ config) cs max-cs)
    ≡⟨ Eq.cong₂ find-or-last refl (Eq.cong₂ _∷_ (preserves-⊇ (sucs n) c max-c config) (zipWith-cong (sucs n) (λ e max-e → preserves-⊇ (sucs n) e max-e config) cs max-cs)) ⟩
      find-or-last (config d) (⟦ translate (sucs n) c max-c ⟧ₙ (conf (sucs n) config) ∷ zipWith (sucs n) (λ e max-e → ⟦ translate (sucs n) e max-e ⟧ₙ (conf (sucs n) config)) cs max-cs)
    ≡˘⟨ Eq.cong₂ find-or-last refl (Eq.cong₂ _∷_ refl (map∘zipWith (sucs n) cs max-cs)) ⟩
      find-or-last (config d) (⟦ translate (sucs n) c max-c ⟧ₙ (conf (sucs n) config) ∷ List.map (λ e → ⟦ e ⟧ₙ (conf (sucs n) config)) (zipWith (sucs n) (translate (sucs n)) cs max-cs))
    ≡˘⟨ map-find-or-last (λ e → ⟦ e ⟧ₙ (conf (sucs n) config)) (config d) (translate (sucs n) c max-c ∷ zipWith (sucs n) (translate (sucs n)) cs max-cs) ⟩
      ⟦ find-or-last (config d) (translate (sucs n) c max-c ∷ zipWith (sucs n) (translate (sucs n)) cs max-cs) ⟧ₙ (conf (sucs n) config)
    ≡⟨ Eq.cong₂ ⟦_⟧ₙ (find-or-last⇒lookup (translate (sucs n) c max-c) (zipWith (sucs n) (translate (sucs n)) cs max-cs)) refl ⟩
      ⟦ Vec.lookup (translate (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs)) (ℕ≥.cappedFin (config d)) ⟧ₙ (conf (sucs n) config)
    ≡˘⟨ Eq.cong₂ ⟦_⟧ₙ (Eq.cong₂ Vec.lookup (refl {x = translate (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs)}) (ℕ≥.cast-cappedFin (config d) (Eq.sym (Eq.cong suc (length-zipWith (sucs n) cs max-cs))))) refl ⟩
      ⟦ Vec.lookup (translate (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs)) (Fin.cast (Eq.sym (Eq.cong suc (length-zipWith (sucs n) cs max-cs))) (ℕ≥.cappedFin (config d))) ⟧ₙ (conf (sucs n) config)
    ≡˘⟨ Eq.cong₂ ⟦_⟧ₙ (Vec.lookup-cast₁ (Eq.cong suc (length-zipWith (sucs n) cs max-cs)) (translate (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs)) (ℕ≥.cappedFin (config d))) refl ⟩
      ⟦ Vec.lookup (Vec.cast (Eq.cong suc (length-zipWith (sucs n) cs max-cs)) (translate (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs))) (ℕ≥.cappedFin (config d)) ⟧ₙ (conf (sucs n) config)
    ≡⟨⟩
      ⟦ Vec.lookup (translate (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs))) (ℕ≥.cappedFin (config d)) ⟧ₙ (conf (sucs n) config)
    ≡˘⟨ Eq.cong₂ ⟦_⟧ₙ (Eq.cong₂ Vec.lookup (refl {x = translate (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs))}) (ℕ≥.cappedFin-idempotent max≤n (config d))) refl ⟩
      ⟦ Vec.lookup (translate (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs))) (ℕ≥.cappedFin (Fin.toℕ (conf (sucs n) config d))) ⟧ₙ (conf (sucs n) config)
    ≡˘⟨ Eq.cong₂ ⟦_⟧ₙ (Vec.lookup-saturate (s≤s max≤n) (translate (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs))) (conf (sucs n) config d)) refl ⟩
      ⟦ Vec.lookup (Vec.saturate (s≤s max≤n) (translate (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs)))) (conf (sucs n) config d) ⟧ₙ (conf (sucs n) config)
    ≡⟨⟩
      ⟦ d ⟨ Vec.saturate (s≤s max≤n) (translate (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs))) ⟩ ⟧ₙ (conf (sucs n) config)
    ≡⟨⟩
      ⟦ translate (sucs n) (d ⟨ c ∷ cs ⟩) (maxChoice (s≤s max≤n) (max-c ∷ max-cs)) ⟧ₙ (conf (sucs n) config)
    ∎

  preserves : ∀ {i : Size} {D A : Set}
    → (n : ℕ≥ 2)
    → (expr : CCC D i A)
    → (choiceLengthLimit : ChoiceLengthLimit n expr)
    → ⟦ translate n expr choiceLengthLimit ⟧ₙ ≅[ fnoc n ][ conf n ] ⟦ expr ⟧ₐ
  preserves n expr choiceLengthLimit = preserves-⊆ n expr choiceLengthLimit , preserves-⊇ n expr choiceLengthLimit

  -- Can't instantiate a LanguageCompiler because the expression compiler depends on the expression

  -- CCC→NCC : {i : Size} → {D : Set} → LanguageCompiler (CCCL D {i}) (λ e → NCCL (maxChoiceLength e) D)
  -- CCC→NCC n .LanguageCompiler.compile expr = translate (maxChoiceLength expr) expr (maxChoiceLengthLimit expr)
  -- CCC→NCC n .LanguageCompiler.config-compiler expr .to = conf (maxChoiceLength expr)
  -- CCC→NCC n .LanguageCompiler.config-compiler expr .from = fnoc (maxChoiceLength expr)
  -- CCC→NCC n .LanguageCompiler.preserves expr = ≅[]-sym (preserves (maxChoiceLength expr) expr (maxChoiceLengthIsLimit expr))


Fin→ℕ : ∀ {D : Set} → (n : ℕ≥ 2) -> IndexedDimension D n → D × ℕ
Fin→ℕ n (d , i) = (d , Fin.toℕ i)

Fin→ℕ⁻¹ : ∀ {D : Set} → (n : ℕ≥ 2) -> D × ℕ → IndexedDimension D n
Fin→ℕ⁻¹ n (d , i) = (d , ℕ≥.cappedFin {ℕ≥.pred n} i)

translate : ∀ {i : Size} {D A : Set}
  → (n : ℕ≥ 2)
  → (expr : CCC D i A)
  → NCC n (D × ℕ) ∞ A
translate (sucs n) expr = NCC-map-dim.compile (sucs n) (Fin→ℕ (Exact.maxChoiceLength expr)) (Fin→ℕ⁻¹ (Exact.maxChoiceLength expr)) (λ where (d , i) → Eq.cong₂ _,_ refl (lemma (Exact.maxChoiceLength expr) i)) (NCC→NCC.compile (Exact.maxChoiceLength expr) (sucs n) (Exact.translate (Exact.maxChoiceLength expr) expr (Exact.maxChoiceLengthIsLimit expr)))
  where
  lemma : (n : ℕ≥ 2) → (i : Fin (ℕ≥.toℕ (ℕ≥.pred n))) → ℕ≥.cappedFin {ℕ≥.pred n} (Fin.toℕ i) ≡ i
  lemma (sucs n) i = ℕ≥.cappedFin-toℕ i

conf : ∀ {i : Size} {D A : Set}
  → (n : ℕ≥ 2)
  → (expr : CCC D i A)
  → CCC.Configuration D
  → NCC.Configuration n (D × ℕ)
conf n expr = (NCCꟲ-map-dim n (Fin→ℕ⁻¹ (Exact.maxChoiceLength expr))) ∘ NCC→NCC.conf (Exact.maxChoiceLength expr) n (Exact.translate (Exact.maxChoiceLength expr) expr (Exact.maxChoiceLengthIsLimit expr)) ∘ Exact.conf (Exact.maxChoiceLength expr)

fnoc : ∀ {i : Size} {D A : Set}
  → (n : ℕ≥ 2)
  → (expr : CCC D i A)
  → NCC.Configuration n (D × ℕ)
  → CCC.Configuration D
fnoc n expr = Exact.fnoc (Exact.maxChoiceLength expr) ∘ NCC→NCC.fnoc (Exact.maxChoiceLength expr) n (Exact.translate (Exact.maxChoiceLength expr) expr (Exact.maxChoiceLengthIsLimit expr)) ∘ (NCCꟲ-map-dim n (Fin→ℕ (Exact.maxChoiceLength expr)))

preserves : ∀ {i : Size} {D A : Set}
  → (n : ℕ≥ 2)
  → (expr : CCC D i A)
  → ⟦ translate n expr ⟧ₙ ≅[ fnoc n expr ][ conf n expr ] ⟦ expr ⟧ₐ
preserves (sucs n) expr =
  ⟦ translate (sucs n) expr ⟧ₙ
  ≅[]⟨⟩
  ⟦ NCC-map-dim.compile (sucs n) (Fin→ℕ (Exact.maxChoiceLength expr)) (Fin→ℕ⁻¹ (Exact.maxChoiceLength expr)) (λ where (d , i) → Eq.cong₂ _,_ refl (lemma (Exact.maxChoiceLength expr) i)) (NCC→NCC.compile (Exact.maxChoiceLength expr) (sucs n) (Exact.translate (Exact.maxChoiceLength expr) expr (Exact.maxChoiceLengthIsLimit expr))) ⟧ₙ
  ≅[]˘⟨ NCC-map-dim.preserves (sucs n) (Fin→ℕ (Exact.maxChoiceLength expr)) (Fin→ℕ⁻¹ (Exact.maxChoiceLength expr)) (λ where (d , i) → Eq.cong₂ _,_ refl (lemma (Exact.maxChoiceLength expr) i)) (NCC→NCC.compile (Exact.maxChoiceLength expr) (sucs n) (Exact.translate (Exact.maxChoiceLength expr) expr (Exact.maxChoiceLengthIsLimit expr))) ⟩
  ⟦ NCC→NCC.compile (Exact.maxChoiceLength expr) (sucs n) (Exact.translate (Exact.maxChoiceLength expr) expr (Exact.maxChoiceLengthIsLimit expr)) ⟧ₙ
  ≅[]˘⟨ (NCC→NCC.preserves (Exact.maxChoiceLength expr) (sucs n) (Exact.translate (Exact.maxChoiceLength expr) expr (Exact.maxChoiceLengthIsLimit expr))) ⟩
  ⟦ Exact.translate (Exact.maxChoiceLength expr) expr (Exact.maxChoiceLengthIsLimit expr) ⟧ₙ
  ≅[]⟨ Exact.preserves (Exact.maxChoiceLength expr) expr (Exact.maxChoiceLengthIsLimit expr) ⟩
    ⟦ expr ⟧ₐ
  ≅[]-∎
  where
  lemma : (n : ℕ≥ 2) → (i : Fin (ℕ≥.toℕ (ℕ≥.pred n))) → ℕ≥.cappedFin {ℕ≥.pred n} (Fin.toℕ i) ≡ i
  lemma (sucs n) i = ℕ≥.cappedFin-toℕ i

CCC→NCC : ∀ {i : Size} {D : Set} → (n : ℕ≥ 2) → LanguageCompiler (CCCL D {i}) (NCCL n (D × ℕ))
CCC→NCC n .LanguageCompiler.compile = translate n
CCC→NCC n .LanguageCompiler.config-compiler expr .to = conf n expr
CCC→NCC n .LanguageCompiler.config-compiler expr .from = fnoc n expr
CCC→NCC n .LanguageCompiler.preserves expr = ≅[]-sym (preserves n expr)

NCC≽CCC : ∀ {D : Set} → (n : ℕ≥ 2) → NCCL n (D × ℕ) ≽ CCCL D
NCC≽CCC n = expressiveness-from-compiler (CCC→NCC n)
