module Translation.Lang.CCC-to-NCC where

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
open import Framework.Definitions using (𝔽; 𝔸; atoms)
open import Framework.Relation.Expressiveness using (expressiveness-from-compiler; _≽_)
open import Framework.Relation.Function using (from; to)
open import Framework.VariabilityLanguage using (artifact)
open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≗_)
open import Size using (Size; ↑_; ∞)
open import Util.List using (find-or-last; map-find-or-last; find-or-last⇒lookup)
open import Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs; _⊔_)
import Util.Vec as Vec

open Eq.≡-Reasoning using (step-≡-⟨; step-≡-⟩; step-≡-∣; _∎)
open IndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-sym)
open IndexedSet.≅[]-Reasoning using (step-≅[]-⟨; step-≅[]-⟩; _≅[]⟨⟩_; _≅[]-∎)

open import Lang.All
open CCC using (CCC; CCCL; _-<_>-; _⟨_⟩)
open NCC using (NCC; NCCL; _-<_>-; _⟨_⟩)

open import Framework.Annotation.IndexedDimension
open import Translation.Lang.NCC.NCC-to-NCC using (NCC→NCC)
open import Translation.Lang.NCC.Rename using (NCC-rename; NCC-map-config)
module NCC-rename {i} {D₁} {D₂} n f f⁻¹ is-inverse = LanguageCompiler (NCC-rename {i} {D₁} {D₂} n f f⁻¹ is-inverse)
module NCC→NCC {i} {D} n m = LanguageCompiler (NCC→NCC {i} {D} n m)

module Exact where
  -- Idea of this translation:
  -- We want to extend the list of alternatives in each choice of a `CCC` expression to such that they all have the same length.
  -- The saturated semantics of `CCC` (see `find-or-last`) ensures that, by reusing the last element, the semantic of the expression doesn't change.
  -- Such a saturated `CCC` expression can then be translated into a `NCC` expression by converting the alternative lists into vectors.
  -- However, the arity of the `NCC` language is the length of these vectors, which depends on the length of the alternative lists in the unsaturated `CCC` expression.
  -- Hence, we need to calculate the maximum choice length (`⌈_⌉`) and a proof (`NumberOfAlternatives≤`) that all choice lengths are smaller than that (`numberOfAlternatives≤⌈_⌉`).

  maximum : List (ℕ≥ 2) → ℕ≥ 2
  maximum [] = sucs zero
  maximum (n ∷ ns) = n ⊔ maximum ns

  maximum⁺ : List⁺ (ℕ≥ 2) → ℕ≥ 2
  maximum⁺ (n ∷ ns) = maximum (n ∷ ns)

  -- Calculcates the `maximum number of alternatives ⊔ 2`.
  -- We want to translate into `NCC` which has an arity of at leat 2 so we
  -- ensure that the result is ≥ 2
  ⌈_⌉ : ∀ {i : Size} {D : 𝔽} {A : 𝔸} → CCC D i A → ℕ≥ 2
  ⌈ a -< cs >-         ⌉ = maximum (List.map ⌈_⌉ cs)
  ⌈ d ⟨ c ∷ [] ⟩       ⌉ = ⌈ c ⌉
  ⌈ d ⟨ c₁ ∷ c₂ ∷ cs ⟩ ⌉ = sucs (List.length cs) ⊔ maximum⁺ (List⁺.map ⌈_⌉ (c₁ ∷ c₂ ∷ cs))

  mutual
    -- A proof that an expression's longest alternative list is at maximum `n`.
    data NumberOfAlternatives≤ {D : 𝔽} {A : 𝔸} (n : ℕ≥ 2) : {i : Size} → CCC D i A → Set where
      maxArtifact : {i : Size} → {a : atoms A} → {cs : List (CCC D i A)} → NumberOfAlternatives≤-List n {i} cs → NumberOfAlternatives≤ n {↑ i} (a -< cs >-)
      maxChoice : {i : Size} → {d : D} → {cs : List⁺ (CCC D i A)} → List⁺.length cs ≤ ℕ≥.toℕ n → NumberOfAlternatives≤-List⁺ n {i} cs → NumberOfAlternatives≤ n {↑ i} (d ⟨ cs ⟩)

    data NumberOfAlternatives≤-List {D : 𝔽} {A : 𝔸} (n : ℕ≥ 2) : {i : Size} → List (CCC D i A) → Set where
      [] : {i : Size} → NumberOfAlternatives≤-List n {i} []
      _∷_ : {i : Size} → {c : CCC D i A} → {cs : List (CCC D i A)} → NumberOfAlternatives≤ n {i} c → NumberOfAlternatives≤-List n {i} cs → NumberOfAlternatives≤-List n {i} (c ∷ cs)

    data NumberOfAlternatives≤-List⁺ {D : 𝔽} {A : 𝔸} (n : ℕ≥ 2) : {i : Size} → List⁺ (CCC D i A) → Set where
      _∷_ : {i : Size} → {c : CCC D i A} → {cs : List (CCC D i A)} → NumberOfAlternatives≤ n {i} c → NumberOfAlternatives≤-List n {i} cs → NumberOfAlternatives≤-List⁺ n {i} (c ∷ cs)

  mutual
    NumberOfAlternatives≤-respects-≤ : ∀ {i : Size} {D : 𝔽} {A : 𝔸} {cs : CCC D i A} {n₁ n₂ : ℕ≥ 2}
      → n₁ ℕ≥.≤ n₂
      → NumberOfAlternatives≤ n₁ cs
      → NumberOfAlternatives≤ n₂ cs
    NumberOfAlternatives≤-respects-≤ n₁≤n₂ (maxArtifact max-cs) = maxArtifact (NumberOfAlternatives≤-List-respects-≤ n₁≤n₂ max-cs)
    NumberOfAlternatives≤-respects-≤ {cs = d ⟨ cs ⟩} {n₁ = n₁} {n₂ = n₂} n₁≤n₂ (maxChoice max-cs≤n max-cs) = maxChoice (≤-trans max-cs≤n n₁≤n₂) (NumberOfAlternatives≤-List⁺-respects-≤ n₁≤n₂ max-cs)

    NumberOfAlternatives≤-List-respects-≤ : ∀ {i : Size} {D : 𝔽} {A : 𝔸} {cs : List (CCC D i A)} {n₁ n₂ : ℕ≥ 2}
      → n₁ ℕ≥.≤ n₂
      → NumberOfAlternatives≤-List n₁ cs
      → NumberOfAlternatives≤-List n₂ cs
    NumberOfAlternatives≤-List-respects-≤ n₁≤n₂ [] = []
    NumberOfAlternatives≤-List-respects-≤ n₁≤n₂ (c ∷ cs) = NumberOfAlternatives≤-respects-≤ n₁≤n₂ c ∷ NumberOfAlternatives≤-List-respects-≤ n₁≤n₂ cs

    NumberOfAlternatives≤-List⁺-respects-≤ : ∀ {i : Size} {D : 𝔽} {A : 𝔸} {cs : List⁺ (CCC D i A)} {n₁ n₂ : ℕ≥ 2}
      → n₁ ℕ≥.≤ n₂
      → NumberOfAlternatives≤-List⁺ n₁ cs
      → NumberOfAlternatives≤-List⁺ n₂ cs
    NumberOfAlternatives≤-List⁺-respects-≤ n₁≤n₂ (c ∷ cs) = NumberOfAlternatives≤-respects-≤ n₁≤n₂ c ∷ NumberOfAlternatives≤-List-respects-≤ n₁≤n₂ cs

  mutual
    -- Proof that `⌈_⌉` calculates a correct choice lenght limit.
    numberOfAlternatives≤⌈_⌉ : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
      → (expr : CCC D i A)
      → NumberOfAlternatives≤ ⌈ expr ⌉ expr
    numberOfAlternatives≤⌈_⌉ (a -< cs >-) = maxArtifact (numberOfAlternatives≤⌈_⌉-List cs)
    numberOfAlternatives≤⌈_⌉ (d ⟨ c ∷ [] ⟩) = maxChoice (≤-trans (ℕ.n≤1+n 1) (ℕ≥.≤-toℕ ⌈ c ⌉)) (numberOfAlternatives≤⌈_⌉ c ∷ [])
    numberOfAlternatives≤⌈_⌉ (d ⟨ c₁ ∷ c₂ ∷ cs ⟩) = maxChoice (ℕ≥.m≤m⊔n (sucs (List.length cs)) (maximum⁺ (List⁺.map ⌈_⌉ (c₁ ∷ c₂ ∷ cs)))) (NumberOfAlternatives≤-List⁺-respects-≤ (ℕ≥.m≤n⊔m (sucs (List.length cs)) (maximum⁺ (List⁺.map ⌈_⌉ (c₁ ∷ c₂ ∷ cs)))) (numberOfAlternatives≤⌈_⌉-List⁺ (c₁ ∷ c₂ ∷ cs)))

    numberOfAlternatives≤⌈_⌉-List : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
      → (cs : List (CCC D i A))
      → NumberOfAlternatives≤-List (maximum (List.map ⌈_⌉ cs)) cs
    numberOfAlternatives≤⌈_⌉-List [] = []
    numberOfAlternatives≤⌈_⌉-List (c ∷ cs) = NumberOfAlternatives≤-respects-≤ (ℕ≥.m≤m⊔n ⌈ c ⌉ (maximum (List.map ⌈_⌉ cs))) (numberOfAlternatives≤⌈_⌉ c) ∷ NumberOfAlternatives≤-List-respects-≤ (ℕ≥.m≤n⊔m ⌈ c ⌉ (maximum (List.map ⌈_⌉ cs))) (numberOfAlternatives≤⌈_⌉-List cs)

    numberOfAlternatives≤⌈_⌉-List⁺ : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
      → (cs : List⁺ (CCC D i A))
      → NumberOfAlternatives≤-List⁺ (maximum⁺ (List⁺.map ⌈_⌉ cs)) cs
    numberOfAlternatives≤⌈_⌉-List⁺ (c ∷ cs) with numberOfAlternatives≤⌈_⌉-List (c ∷ cs)
    ... | max-c ∷ max-cs = max-c ∷ max-cs

  mutual
    translate : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
      → (n : ℕ≥ 2)
      → (expr : CCC D i A)
      → NumberOfAlternatives≤ n {i} expr
      → NCC n D i A
    translate n (a -< cs >-) (maxArtifact max-cs) = a -< zipWith n (translate n) cs max-cs >-
    translate (sucs n) (d ⟨ c ∷ cs ⟩) (maxChoice max≤n (max-c ∷ max-cs)) =
      d ⟨ Vec.saturate max≤n (translate (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs))) ⟩

    -- TODO Can probably be generalized
    zipWith : ∀ {i : Size} {D : 𝔽} {A : 𝔸} {Result : Set}
      → (n : ℕ≥ 2)
      → ((expr : CCC D i A) → NumberOfAlternatives≤ n expr → Result)
      → (cs : List (CCC D i A))
      → NumberOfAlternatives≤-List n cs
      → List Result
    zipWith n f [] [] = []
    zipWith n f (c ∷ cs) (max-c ∷ max-cs) = f c max-c ∷ zipWith n f cs max-cs

    length-zipWith : ∀ {i : Size} {D : 𝔽} {A : 𝔸} {Result : Set}
      → (n : ℕ≥ 2)
      → {f : (expr : CCC D i A) → NumberOfAlternatives≤ n expr → Result}
      → (cs : List (CCC D i A))
      → (max-cs : NumberOfAlternatives≤-List n cs)
      → List.length (zipWith {i} n f cs max-cs) ≡ List.length cs
    length-zipWith n [] [] = refl
    length-zipWith n (c ∷ cs) (max-c ∷ max-cs) = Eq.cong suc (length-zipWith n cs max-cs)

  map∘zipWith : ∀ {i : Size} {D : 𝔽} {A : 𝔸} {Result₁ Result₂ : Set}
    → (n : ℕ≥ 2)
    → {g : Result₁ → Result₂}
    → {f : (expr : CCC D i A) → NumberOfAlternatives≤ n expr → Result₁}
    → (cs : List (CCC D i A))
    → (max-cs : NumberOfAlternatives≤-List n cs)
    → List.map g (zipWith n f cs max-cs) ≡ zipWith n (λ e max-e → g (f e max-e)) cs max-cs
  map∘zipWith n [] [] = refl
  map∘zipWith n (c ∷ cs) (max-c ∷ max-cs) = Eq.cong₂ _∷_ refl (map∘zipWith n cs max-cs)

  zipWith-cong : ∀ {i : Size} {D : 𝔽} {A : 𝔸} {Result : Set}
    → (n : ℕ≥ 2)
    → {f g : (expr : CCC D i A) → NumberOfAlternatives≤ n expr → Result}
    → ((e : CCC D i A) → (max-e : NumberOfAlternatives≤ n e) → f e max-e ≡ g e max-e)
    → (cs : List (CCC D i A))
    → (max-cs : NumberOfAlternatives≤-List n cs)
    → zipWith n f cs max-cs ≡ zipWith n g cs max-cs
  zipWith-cong n f≗g [] [] = refl
  zipWith-cong n f≗g (c ∷ cs) (max-c ∷ max-cs) = Eq.cong₂ _∷_ (f≗g c max-c) (zipWith-cong n f≗g cs max-cs)

  zipWith⇒map : ∀ {i : Size} {D : 𝔽} {A : 𝔸} {Result : Set}
    → (n : ℕ≥ 2)
    → (f : (expr : CCC D i A) → Result)
    → (cs : List (CCC D i A))
    → (max-cs : NumberOfAlternatives≤-List n cs)
    → zipWith n (λ e max-e → f e) cs max-cs ≡ List.map f cs
  zipWith⇒map n f [] [] = refl
  zipWith⇒map n f (c ∷ cs) (max-c ∷ max-cs) = Eq.cong₂ _∷_ refl (zipWith⇒map n f cs max-cs)


  conf : ∀ {D : 𝔽} → (n : ℕ≥ 2) → CCC.Configuration D → NCC.Configuration n D
  conf (sucs n) config d = ℕ≥.cappedFin (config d)

  fnoc : ∀ {D : 𝔽} → (n : ℕ≥ 2) → NCC.Configuration n D → CCC.Configuration D
  fnoc n config d = Fin.toℕ (config d)

  preserves-⊆ : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
    → (n : ℕ≥ 2)
    → (expr : CCC D i A)
    → (choiceLengthLimit : NumberOfAlternatives≤ n expr)
    → NCC.⟦ translate n expr choiceLengthLimit ⟧ ⊆[ fnoc n ] CCC.⟦ expr ⟧
  preserves-⊆ n (a -< cs >-) (maxArtifact max-cs) config =
      NCC.⟦ translate n (a -< cs >-) (maxArtifact max-cs) ⟧ config
    ≡⟨⟩
      NCC.⟦ a -< zipWith n (translate n) cs max-cs >- ⟧ config
    ≡⟨⟩
      artifact a (List.map (λ e → NCC.⟦ e ⟧ config) (zipWith n (translate n) cs max-cs))
    ≡⟨ Eq.cong₂ artifact refl (map∘zipWith n cs max-cs) ⟩
      artifact a (zipWith n (λ e max-e → NCC.⟦ translate n e max-e ⟧ config) cs max-cs)
    ≡⟨ Eq.cong₂ artifact refl (zipWith-cong n (λ e max-e → preserves-⊆ n e max-e config) cs max-cs) ⟩
      artifact a (zipWith n (λ e max-e → CCC.⟦ e ⟧ (fnoc n config)) cs max-cs)
    ≡⟨ Eq.cong₂ artifact refl (zipWith⇒map n (λ e → CCC.⟦ e ⟧ (fnoc n config)) cs max-cs) ⟩
      artifact a (List.map (λ e → CCC.⟦ e ⟧ (fnoc n config)) cs)
    ≡⟨⟩
      CCC.⟦ a -< cs >- ⟧ (fnoc n config)
    ∎
  preserves-⊆ (sucs n) (d ⟨ c ∷ cs ⟩) (maxChoice max≤n (max-c ∷ max-cs)) config =
      NCC.⟦ translate (sucs n) (d ⟨ c ∷ cs ⟩) (maxChoice (max≤n) (max-c ∷ max-cs)) ⟧ config
    ≡⟨⟩
      NCC.⟦ d ⟨ Vec.saturate max≤n (translate (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs))) ⟩ ⟧ config
    ≡⟨⟩
      NCC.⟦ Vec.lookup (Vec.saturate max≤n (translate (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs)))) (config d) ⟧ config
    ≡⟨ Eq.cong₂ NCC.⟦_⟧ (Vec.lookup-saturate max≤n (translate (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs))) (config d)) refl ⟩
      NCC.⟦ Vec.lookup (translate (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs))) (ℕ≥.cappedFin (Fin.toℕ (config d))) ⟧ config
    ≡⟨⟩
      NCC.⟦ Vec.lookup (Vec.cast (Eq.cong suc (length-zipWith (sucs n) cs max-cs)) (translate (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs))) (ℕ≥.cappedFin (Fin.toℕ (config d))) ⟧ config
    ≡⟨ Eq.cong₂ NCC.⟦_⟧ (Vec.lookup-cast₁ (Eq.cong suc (length-zipWith (sucs n) cs max-cs)) (translate (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs)) (ℕ≥.cappedFin (Fin.toℕ (config d)))) refl ⟩
      NCC.⟦ Vec.lookup (translate (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs)) (Fin.cast (Eq.sym (Eq.cong suc (length-zipWith (sucs n) cs max-cs))) (ℕ≥.cappedFin (Fin.toℕ (config d)))) ⟧ config
    ≡⟨ Eq.cong₂ NCC.⟦_⟧ (Eq.cong₂ Vec.lookup (refl {x = translate (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs)}) (ℕ≥.cast-cappedFin (Fin.toℕ (config d)) (Eq.sym (Eq.cong suc (length-zipWith (sucs n) cs max-cs))))) refl ⟩
      NCC.⟦ Vec.lookup (translate (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs)) (ℕ≥.cappedFin (Fin.toℕ (config d))) ⟧ config
    ≡⟨ Eq.cong₂ NCC.⟦_⟧ (find-or-last⇒lookup (translate (sucs n) c max-c) (zipWith (sucs n) (translate (sucs n)) cs max-cs)) refl ⟨
      NCC.⟦ find-or-last (Fin.toℕ (config d)) (translate (sucs n) c max-c ∷ zipWith (sucs n) (translate (sucs n)) cs max-cs) ⟧ config
    ≡⟨ map-find-or-last (λ e → NCC.⟦ e ⟧ config) (Fin.toℕ (config d)) (translate (sucs n) c max-c ∷ zipWith (sucs n) (translate (sucs n)) cs max-cs) ⟩
      find-or-last (Fin.toℕ (config d)) (NCC.⟦ translate (sucs n) c max-c ⟧ config ∷ List.map (λ e → NCC.⟦ e ⟧ config) (zipWith (sucs n) (translate (sucs n)) cs max-cs))
    ≡⟨ Eq.cong₂ find-or-last refl (Eq.cong₂ _∷_ refl (map∘zipWith (sucs n) cs max-cs)) ⟩
      find-or-last (Fin.toℕ (config d)) (NCC.⟦ translate (sucs n) c max-c ⟧ config ∷ zipWith (sucs n) (λ e max-e → NCC.⟦ translate (sucs n) e max-e ⟧ config) cs max-cs)
    ≡⟨ Eq.cong₂ find-or-last refl (Eq.cong₂ _∷_ (preserves-⊆ (sucs n) c max-c config) (zipWith-cong (sucs n) (λ e max-e → preserves-⊆ (sucs n) e max-e config) cs max-cs)) ⟩
      find-or-last (Fin.toℕ (config d)) (CCC.⟦ c ⟧ (fnoc (sucs n) config) ∷ zipWith (sucs n) (λ e max-e → CCC.⟦ e ⟧ (fnoc (sucs n) config)) cs max-cs)
    ≡⟨ Eq.cong₂ find-or-last refl (Eq.cong₂ _∷_ refl (zipWith⇒map (sucs n) (λ e → CCC.⟦ e ⟧ (fnoc (sucs n) config)) cs max-cs)) ⟩
      find-or-last (Fin.toℕ (config d)) (CCC.⟦ c ⟧ (fnoc (sucs n) config) ∷ List.map (λ e → CCC.⟦ e ⟧ (fnoc (sucs n) config)) cs)
    ≡⟨⟩
      find-or-last (Fin.toℕ (config d)) (List⁺.map (λ e → CCC.⟦ e ⟧ (fnoc (sucs n) config)) (c ∷ cs))
    ≡⟨ map-find-or-last (λ e → CCC.⟦ e ⟧ (fnoc (sucs n) config)) (fnoc (sucs n) config d) (c ∷ cs) ⟨
      CCC.⟦ find-or-last (fnoc (sucs n) config d) (c ∷ cs) ⟧ (fnoc (sucs n) config)
    ≡⟨⟩
      CCC.⟦ d ⟨ c ∷ cs ⟩ ⟧ (fnoc (sucs n) config)
    ∎

  preserves-⊇ : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
    → (n : ℕ≥ 2)
    → (expr : CCC D i A)
    → (choiceLengthLimit : NumberOfAlternatives≤ n {i} expr)
    → CCC.⟦ expr ⟧ ⊆[ conf n ] NCC.⟦ translate n expr choiceLengthLimit ⟧
  preserves-⊇ n (a -< cs >-) (maxArtifact max-cs) config =
      CCC.⟦ a -< cs >- ⟧ config
    ≡⟨⟩
      artifact a (List.map (λ e → CCC.⟦ e ⟧ config) cs)
    ≡⟨ Eq.cong₂ artifact refl (zipWith⇒map n (λ e → CCC.⟦ e ⟧ config) cs max-cs) ⟨
      artifact a (zipWith n (λ e max-e → CCC.⟦ e ⟧ config) cs max-cs)
    ≡⟨ Eq.cong₂ artifact refl (zipWith-cong n (λ e max-e → preserves-⊇ n e max-e config) cs max-cs) ⟩
      artifact a (zipWith n (λ e max-e → NCC.⟦ translate n e max-e ⟧ (conf n config)) cs max-cs)
    ≡⟨ Eq.cong₂ artifact refl (map∘zipWith n cs max-cs) ⟨
      artifact a (List.map (λ e → NCC.⟦ e ⟧ (conf n config)) (zipWith n (translate n) cs max-cs))
    ≡⟨⟩
      NCC.⟦ a -< zipWith n (translate n) cs max-cs >- ⟧ (conf n config)
    ≡⟨⟩
      NCC.⟦ translate n (a -< cs >-) (maxArtifact max-cs) ⟧ (conf n config)
    ∎
  preserves-⊇ (sucs n) (d ⟨ c ∷ cs ⟩) (maxChoice (s≤s max≤n) (max-c ∷ max-cs)) config =
      CCC.⟦ d ⟨ c ∷ cs ⟩ ⟧ config
    ≡⟨⟩
      CCC.⟦ find-or-last (config d) (c ∷ cs) ⟧ config
    ≡⟨ map-find-or-last (λ e → CCC.⟦ e ⟧ config) (config d) (c ∷ cs) ⟩
      find-or-last (config d) (List⁺.map (λ e → CCC.⟦ e ⟧ config) (c ∷ cs))
    ≡⟨⟩
      find-or-last (config d) (CCC.⟦ c ⟧ config ∷ List.map (λ e → CCC.⟦ e ⟧ config) cs)
    ≡⟨ Eq.cong₂ find-or-last refl (Eq.cong₂ _∷_ refl (zipWith⇒map (sucs n) (λ e → CCC.⟦ e ⟧ config) cs max-cs)) ⟨
      find-or-last (config d) (CCC.⟦ c ⟧ config ∷ zipWith (sucs n) (λ e max-e → CCC.⟦ e ⟧ config) cs max-cs)
    ≡⟨ Eq.cong₂ find-or-last refl (Eq.cong₂ _∷_ (preserves-⊇ (sucs n) c max-c config) (zipWith-cong (sucs n) (λ e max-e → preserves-⊇ (sucs n) e max-e config) cs max-cs)) ⟩
      find-or-last (config d) (NCC.⟦ translate (sucs n) c max-c ⟧ (conf (sucs n) config) ∷ zipWith (sucs n) (λ e max-e → NCC.⟦ translate (sucs n) e max-e ⟧ (conf (sucs n) config)) cs max-cs)
    ≡⟨ Eq.cong₂ find-or-last refl (Eq.cong₂ _∷_ refl (map∘zipWith (sucs n) cs max-cs)) ⟨
      find-or-last (config d) (NCC.⟦ translate (sucs n) c max-c ⟧ (conf (sucs n) config) ∷ List.map (λ e → NCC.⟦ e ⟧ (conf (sucs n) config)) (zipWith (sucs n) (translate (sucs n)) cs max-cs))
    ≡⟨ map-find-or-last (λ e → NCC.⟦ e ⟧ (conf (sucs n) config)) (config d) (translate (sucs n) c max-c ∷ zipWith (sucs n) (translate (sucs n)) cs max-cs) ⟨
      NCC.⟦ find-or-last (config d) (translate (sucs n) c max-c ∷ zipWith (sucs n) (translate (sucs n)) cs max-cs) ⟧ (conf (sucs n) config)
    ≡⟨ Eq.cong₂ NCC.⟦_⟧ (find-or-last⇒lookup (translate (sucs n) c max-c) (zipWith (sucs n) (translate (sucs n)) cs max-cs)) refl ⟩
      NCC.⟦ Vec.lookup (translate (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs)) (ℕ≥.cappedFin (config d)) ⟧ (conf (sucs n) config)
    ≡⟨ Eq.cong₂ NCC.⟦_⟧ (Eq.cong₂ Vec.lookup (refl {x = translate (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs)}) (ℕ≥.cast-cappedFin (config d) (Eq.sym (Eq.cong suc (length-zipWith (sucs n) cs max-cs))))) refl ⟨
      NCC.⟦ Vec.lookup (translate (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs)) (Fin.cast (Eq.sym (Eq.cong suc (length-zipWith (sucs n) cs max-cs))) (ℕ≥.cappedFin (config d))) ⟧ (conf (sucs n) config)
    ≡⟨ Eq.cong₂ NCC.⟦_⟧ (Vec.lookup-cast₁ (Eq.cong suc (length-zipWith (sucs n) cs max-cs)) (translate (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs)) (ℕ≥.cappedFin (config d))) refl ⟨
      NCC.⟦ Vec.lookup (Vec.cast (Eq.cong suc (length-zipWith (sucs n) cs max-cs)) (translate (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs))) (ℕ≥.cappedFin (config d)) ⟧ (conf (sucs n) config)
    ≡⟨⟩
      NCC.⟦ Vec.lookup (translate (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs))) (ℕ≥.cappedFin (config d)) ⟧ (conf (sucs n) config)
    ≡⟨ Eq.cong₂ NCC.⟦_⟧ (Eq.cong₂ Vec.lookup (refl {x = translate (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs))}) (ℕ≥.cappedFin-idempotent max≤n (config d))) refl ⟨
      NCC.⟦ Vec.lookup (translate (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs))) (ℕ≥.cappedFin (Fin.toℕ (conf (sucs n) config d))) ⟧ (conf (sucs n) config)
    ≡⟨ Eq.cong₂ NCC.⟦_⟧ (Vec.lookup-saturate (s≤s max≤n) (translate (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs))) (conf (sucs n) config d)) refl ⟨
      NCC.⟦ Vec.lookup (Vec.saturate (s≤s max≤n) (translate (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs)))) (conf (sucs n) config d) ⟧ (conf (sucs n) config)
    ≡⟨⟩
      NCC.⟦ d ⟨ Vec.saturate (s≤s max≤n) (translate (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs))) ⟩ ⟧ (conf (sucs n) config)
    ≡⟨⟩
      NCC.⟦ translate (sucs n) (d ⟨ c ∷ cs ⟩) (maxChoice (s≤s max≤n) (max-c ∷ max-cs)) ⟧ (conf (sucs n) config)
    ∎

  preserves : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
    → (n : ℕ≥ 2)
    → (expr : CCC D i A)
    → (choiceLengthLimit : NumberOfAlternatives≤ n expr)
    → NCC.⟦ translate n expr choiceLengthLimit ⟧ ≅[ fnoc n ][ conf n ] CCC.⟦ expr ⟧
  preserves n expr choiceLengthLimit = preserves-⊆ n expr choiceLengthLimit , preserves-⊇ n expr choiceLengthLimit

  -- Can't instantiate a LanguageCompiler because the expression compiler depends on the expression

  -- CCC→NCC : {i : Size} → {D : 𝔽} → LanguageCompiler (CCCL D {i}) (λ e → NCCL ⌈ e ⌉ D)
  -- --                                                                ^^^^^^ this unrepresentable in our framework
  -- CCC→NCC n .LanguageCompiler.compile expr = translate ⌈ expr ⌉ expr (numberOfAlternatives≤⌈_⌉ expr)
  -- CCC→NCC n .LanguageCompiler.config-compiler expr .to = conf ⌈ expr ⌉
  -- CCC→NCC n .LanguageCompiler.config-compiler expr .from = fnoc ⌈ expr ⌉
  -- CCC→NCC n .LanguageCompiler.preserves expr = ≅[]-sym (preserves ⌈ expr ⌉ expr (numberOfAlternatives≤⌈_⌉ expr))

  -- Having the output language depend on the input expression brings along a lot of complications and problems.
  -- Introducing such complications can be avoided by generalizing `translate` to translate into an arbitrary ary `NCCL` by composing it with `NCC→NCC`.
  -- This is implemented in the rest of this file.


open Exact using (⌈_⌉; numberOfAlternatives≤⌈_⌉)

-- Gets rid of the `⌈_⌉` in the `IndexedDimension`, here `n`.
Fin→ℕ : ∀ {D : 𝔽} → (n : ℕ≥ 2) -> IndexedDimension D n → D × ℕ
Fin→ℕ n (d , i) = (d , Fin.toℕ i)

Fin→ℕ⁻¹ : ∀ {D : 𝔽} → (n : ℕ≥ 2) -> D × ℕ → IndexedDimension D n
Fin→ℕ⁻¹ n (d , i) = (d , ℕ≥.cappedFin {ℕ≥.pred n} i)

Fin→ℕ⁻¹-Fin→ℕ : ∀ {D : 𝔽} → (n : ℕ≥ 2) → Fin→ℕ⁻¹ {D} n ∘ Fin→ℕ {D} n ≗ id
Fin→ℕ⁻¹-Fin→ℕ (sucs n) (d , i) = Eq.cong₂ _,_ refl (ℕ≥.cappedFin-toℕ i)

translate : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
  → (n : ℕ≥ 2)
  → CCC D i A
  → NCC n (D × ℕ) ∞ A
translate (sucs n) expr =
  NCC-rename.compile (sucs n) (Fin→ℕ ⌈ expr ⌉) (Fin→ℕ⁻¹ ⌈ expr ⌉) (Fin→ℕ⁻¹-Fin→ℕ ⌈ expr ⌉)
    (NCC→NCC.compile ⌈ expr ⌉ (sucs n)
      (Exact.translate ⌈ expr ⌉ expr (numberOfAlternatives≤⌈_⌉ expr)))

conf : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
  → (n : ℕ≥ 2)
  → CCC D i A
  → CCC.Configuration D
  → NCC.Configuration n (D × ℕ)
conf n expr =
  NCC-map-config n (Fin→ℕ⁻¹ ⌈ expr ⌉)
  ∘ NCC→NCC.conf ⌈ expr ⌉ n (Exact.translate ⌈ expr ⌉ expr (numberOfAlternatives≤⌈_⌉ expr))
  ∘ Exact.conf ⌈ expr ⌉

fnoc : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
  → (n : ℕ≥ 2)
  → CCC D i A
  → NCC.Configuration n (D × ℕ)
  → CCC.Configuration D
fnoc n expr =
  Exact.fnoc ⌈ expr ⌉
  ∘ NCC→NCC.fnoc ⌈ expr ⌉ n (Exact.translate ⌈ expr ⌉ expr (numberOfAlternatives≤⌈_⌉ expr))
  ∘ (NCC-map-config n (Fin→ℕ ⌈ expr ⌉))

preserves : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
  → (n : ℕ≥ 2)
  → (expr : CCC D i A)
  → NCC.⟦ translate n expr ⟧ ≅[ fnoc n expr ][ conf n expr ] CCC.⟦ expr ⟧
preserves (sucs n) expr =
  NCC.⟦ translate (sucs n) expr ⟧
  ≅[]⟨⟩
    NCC.⟦ NCC-rename.compile (sucs n) (Fin→ℕ ⌈ expr ⌉) (Fin→ℕ⁻¹ ⌈ expr ⌉) (Fin→ℕ⁻¹-Fin→ℕ ⌈ expr ⌉) (NCC→NCC.compile ⌈ expr ⌉ (sucs n) (Exact.translate ⌈ expr ⌉ expr (numberOfAlternatives≤⌈_⌉ expr))) ⟧
  ≅[]⟨ NCC-rename.preserves (sucs n) (Fin→ℕ ⌈ expr ⌉) (Fin→ℕ⁻¹ ⌈ expr ⌉) (Fin→ℕ⁻¹-Fin→ℕ ⌈ expr ⌉) (NCC→NCC.compile ⌈ expr ⌉ (sucs n) (Exact.translate ⌈ expr ⌉ expr (numberOfAlternatives≤⌈_⌉ expr))) ⟨
    NCC.⟦ NCC→NCC.compile ⌈ expr ⌉ (sucs n) (Exact.translate ⌈ expr ⌉ expr (numberOfAlternatives≤⌈_⌉ expr)) ⟧
  ≅[]⟨ (NCC→NCC.preserves ⌈ expr ⌉ (sucs n) (Exact.translate ⌈ expr ⌉ expr (numberOfAlternatives≤⌈_⌉ expr))) ⟨
    NCC.⟦ Exact.translate ⌈ expr ⌉ expr (numberOfAlternatives≤⌈_⌉ expr) ⟧
  ≅[]⟨ Exact.preserves ⌈ expr ⌉ expr (numberOfAlternatives≤⌈_⌉ expr) ⟩
    CCC.⟦ expr ⟧
  ≅[]-∎

CCC→NCC : ∀ {i : Size} {D : 𝔽} → (n : ℕ≥ 2) → LanguageCompiler (CCCL {i} D) (NCCL n (D × ℕ))
CCC→NCC n .LanguageCompiler.compile = translate n
CCC→NCC n .LanguageCompiler.config-compiler expr .to = conf n expr
CCC→NCC n .LanguageCompiler.config-compiler expr .from = fnoc n expr
CCC→NCC n .LanguageCompiler.preserves expr = ≅[]-sym (preserves n expr)

NCC≽CCC : ∀ {D : 𝔽} → (n : ℕ≥ 2) → NCCL n (D × ℕ) ≽ CCCL D
NCC≽CCC n = expressiveness-from-compiler (CCC→NCC n)
