{-# OPTIONS --sized-types #-}

open import Framework.Construct using (_∈ₛ_; cons; snoc; id-l)
open import Construct.Artifact as At using () renaming (Syntax to Artifact; _-<_>- to artifact-constructor)

module Translation.Lang.CCC-to-FCC (Variant : Set → Set) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

open import Data.Empty using (⊥-elim)
import Data.EqIndexedSet as IndexedSet
open import Data.Fin as Fin using (Fin; zero; suc)
import Data.Fin.Properties as Fin
open import Data.List as List using (List; []; _∷_)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
import Data.List.Properties as List
open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; s≤s; z≤n; _+_; _∸_)
open import Data.Nat.Properties as ℕ using (≤-refl; ≤-reflexive; ≤-trans; <-trans)
open import Data.Product using (_×_; _,_)
open import Data.Vec as Vec using (Vec; []; _∷_)
import Data.Vec.Properties as Vec
open import Framework.Compiler using (LanguageCompiler)
open import Framework.Relation.Function using (from; to)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; _≗_)
open import Relation.Nullary.Decidable using (yes; no)
open import Size using (Size; ↑_; ∞)
import Util.AuxProofs as ℕ
open import Util.List using (find-or-last; map-find-or-last; find-or-last⇒lookup; lookup⇒find-or-last)
open import Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs; _⊔_)
import Util.Vec as Vec

open Eq.≡-Reasoning using (step-≡; step-≡˘; _≡⟨⟩_; _∎)
open IndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-sym; ≅[]-trans)
open IndexedSet.≅[]-Reasoning using (step-≅[]; _≅[]⟨⟩_; _≅[]-∎)
open IndexedSet.⊆-Reasoning using (step-⊆; _⊆-∎)

open import Lang.CCC renaming (Configuration to CCCꟲ)
open Lang.CCC.Sem using (CCCL)
module CCCSem {A} = Lang.CCC.Sem A Variant Artifact∈ₛVariant
open CCCSem using () renaming (⟦_⟧ to ⟦_⟧ₐ)

import Lang.FCC
module FCC n = Lang.FCC n
open FCC renaming (Configuration to FCCꟲ)
open Lang.FCC.Sem using (FCCL)
module FCCSem {n} {A} = Lang.FCC.Sem n A Variant Artifact∈ₛVariant
open FCCSem using () renaming (⟦_⟧ to ⟦_⟧ₙ)

import Translation.Lang.FCC-to-FCC
open Translation.Lang.FCC-to-FCC Variant Artifact∈ₛVariant using () renaming (translate to FCC→FCC; conf to FCCꟲ→FCCꟲ; fnoc to FCCꟲ→FCCꟲ⁻¹; preserves to FCC→FCC-preserves)
open Translation.Lang.FCC-to-FCC Variant Artifact∈ₛVariant using (IndexedDimension)
open Translation.Lang.FCC-to-FCC.map-dim Variant Artifact∈ₛVariant using () renaming (map-dim to FCC-map-dim; preserves to FCC-map-dim-preserves)

artifact : {A : Set} → A → List (Variant A) → Variant A
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
    ListChoiceLengthLimit-⊔ : {i : Size} → {D A : Set} → {cs : List (CCC D i A)} → {n₁ n₂ : ℕ≥ 2} → ListChoiceLengthLimit n₁ cs → ListChoiceLengthLimit (n₁ ⊔ n₂) cs
    ListChoiceLengthLimit-⊔ [] = []
    ListChoiceLengthLimit-⊔ (c ∷ cs) = ChoiceLengthLimit-⊔ c ∷ ListChoiceLengthLimit-⊔ cs

    List⁺ChoiceLengthLimit-⊔ : {i : Size} → {D A : Set} → {cs : List⁺ (CCC D i A)} → {n₁ n₂ : ℕ≥ 2} → List⁺ChoiceLengthLimit n₁ cs → List⁺ChoiceLengthLimit (n₁ ⊔ n₂) cs
    List⁺ChoiceLengthLimit-⊔ (c ∷ cs) = ChoiceLengthLimit-⊔ c ∷ ListChoiceLengthLimit-⊔ cs

    ChoiceLengthLimit-⊔ : {i : Size} → {D A : Set} → {cs : CCC D i A} → {n₁ n₂ : ℕ≥ 2} → ChoiceLengthLimit n₁ cs → ChoiceLengthLimit (n₁ ⊔ n₂) cs
    ChoiceLengthLimit-⊔ (maxArtifact max-cs) = maxArtifact (ListChoiceLengthLimit-⊔ max-cs)
    ChoiceLengthLimit-⊔ {cs = d ⟨ cs ⟩} {n₁ = n₁} {n₂ = n₂} (maxChoice max-cs≤n max-cs) = maxChoice (≤-trans (ℕ.m≤n⇒m≤n⊔o (ℕ≥.toℕ n₂) max-cs≤n) (≤-reflexive (Eq.sym (ℕ≥.toℕ-⊔ n₁ n₂)))) (List⁺ChoiceLengthLimit-⊔ max-cs)

  -- calculcates the maximum + 2 to ensure that it is ≥ 2
  maximum : List (ℕ≥ 2) → ℕ≥ 2
  maximum [] = sucs zero
  maximum (n ∷ ns) = n ⊔ maximum ns

  maximum⁺ : List⁺ (ℕ≥ 2) → ℕ≥ 2
  maximum⁺ (n ∷ ns) = maximum (n ∷ ns)

  -- calculcates the maximum + 2 to ensure that it is ≥ 2
  maxChoiceLength : {i : Size} → {D A : Set} → CCC D i A → ℕ≥ 2
  maxChoiceLength (a -< cs >-) = maximum (List.map maxChoiceLength cs)
  maxChoiceLength (d ⟨ cs ⟩) = sucs (List⁺.length cs) ⊔ maximum⁺ (List⁺.map maxChoiceLength cs)

  ListChoiceLengthLimit-⊔-comm : {i : Size} → {D A : Set} → {cs : List (CCC D i A)} → {n m : ℕ≥ 2} → ListChoiceLengthLimit (n ⊔ m) cs → ListChoiceLengthLimit (m ⊔ n) cs
  ListChoiceLengthLimit-⊔-comm {cs = cs} {n = n} {m = m} a = Eq.subst (λ e → ListChoiceLengthLimit e cs) (ℕ≥.⊔-comm n m) a

  List⁺ChoiceLengthLimit-⊔-comm : {i : Size} → {D A : Set} → {cs : List⁺ (CCC D i A)} → {n m : ℕ≥ 2} → List⁺ChoiceLengthLimit (n ⊔ m) cs → List⁺ChoiceLengthLimit (m ⊔ n) cs
  List⁺ChoiceLengthLimit-⊔-comm {cs = cs} {n = n} {m = m} a = Eq.subst (λ e → List⁺ChoiceLengthLimit e cs) (ℕ≥.⊔-comm n m) a

  mutual
    maximumIsLimit : {i : Size} → {D A : Set} → (cs : List (CCC D i A)) → ListChoiceLengthLimit (maximum (List.map maxChoiceLength cs)) cs
    maximumIsLimit [] = []
    maximumIsLimit (c ∷ cs) = ChoiceLengthLimit-⊔ (maxChoiceLengthIsLimit c) ∷ ListChoiceLengthLimit-⊔-comm {m = maxChoiceLength c} (ListChoiceLengthLimit-⊔ (maximumIsLimit cs))

    maximum⁺IsLimit : {i : Size} → {D A : Set} (cs : List⁺ (CCC D i A)) → List⁺ChoiceLengthLimit (maximum⁺ (List⁺.map maxChoiceLength cs)) cs
    maximum⁺IsLimit (c ∷ cs) = ChoiceLengthLimit-⊔ (maxChoiceLengthIsLimit c) ∷ ListChoiceLengthLimit-⊔-comm {m = maxChoiceLength c} (ListChoiceLengthLimit-⊔ (maximumIsLimit cs))

    maxChoiceLengthIsLimit : {i : Size} → {D A : Set} → (expr : CCC D i A) → ChoiceLengthLimit (maxChoiceLength expr) expr
    maxChoiceLengthIsLimit (a -< cs >-) = maxArtifact (maximumIsLimit cs)
    maxChoiceLengthIsLimit (d ⟨ cs ⟩) = maxChoice (≤-trans (ℕ.m≤n⇒m≤n⊔o (ℕ≥.toℕ (maximum⁺ (List⁺.map maxChoiceLength cs))) (≤-trans (ℕ.n≤1+n (List⁺.length cs)) (ℕ.n≤1+n (suc (List⁺.length cs))))) (≤-reflexive (Eq.sym (ℕ≥.toℕ-⊔ (sucs (List⁺.length cs)) (maximum⁺ (List⁺.map maxChoiceLength cs)))))) (List⁺ChoiceLengthLimit-⊔-comm (List⁺ChoiceLengthLimit-⊔ (maximum⁺IsLimit cs)))

  mutual
    translate : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → (expr : CCC D i A) → ChoiceLengthLimit n {i} expr → FCC n D i A
    translate n (a -< cs >-) (maxArtifact max-cs) = a -< zipWith n (translate n) cs max-cs >-
    translate (sucs n) (d ⟨ c ∷ cs ⟩) (maxChoice max≤n (max-c ∷ max-cs)) =
      d ⟨ Vec.saturate max≤n (translate (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (translate (sucs n)) cs max-cs))) ⟩

    -- Can probably be generalized
    zipWith : {i : Size} → {D A Result : Set} → (n : ℕ≥ 2) → ((expr : CCC D i A) → ChoiceLengthLimit n expr → Result) → (cs : List (CCC D i A)) → ListChoiceLengthLimit n cs → List Result
    zipWith n f [] [] = []
    zipWith n f (c ∷ cs) (max-c ∷ max-cs) = f c max-c ∷ zipWith n f cs max-cs

    length-zipWith : {i : Size} → {D A Result : Set} → (n : ℕ≥ 2) → {f : (expr : CCC D i A) → ChoiceLengthLimit n expr → Result} → (cs : List (CCC D i A)) → (max-cs : ListChoiceLengthLimit n cs) → List.length (zipWith {i} n f cs max-cs) ≡ List.length cs
    length-zipWith n [] [] = refl
    length-zipWith n (c ∷ cs) (max-c ∷ max-cs) = Eq.cong suc (length-zipWith n cs max-cs)

  map∘zipWith : {i : Size} → {D A Result₁ Result₂ : Set} → (n : ℕ≥ 2) → {g : Result₁ → Result₂} → {f : (expr : CCC D i A) → ChoiceLengthLimit n expr → Result₁} → (cs : List (CCC D i A)) → (max-cs : ListChoiceLengthLimit n cs) → List.map g (zipWith n f cs max-cs) ≡ zipWith n (λ e max-e → g (f e max-e)) cs max-cs
  map∘zipWith n [] [] = refl
  map∘zipWith n (c ∷ cs) (max-c ∷ max-cs) = Eq.cong₂ _∷_ refl (map∘zipWith n cs max-cs)

  zipWith-cong : {i : Size} → {D A Result : Set} → (n : ℕ≥ 2) → {f g : (expr : CCC D i A) → ChoiceLengthLimit n expr → Result} → ((e : CCC D i A) → (max-e : ChoiceLengthLimit n e) → f e max-e ≡ g e max-e) → (cs : List (CCC D i A)) → (max-cs : ListChoiceLengthLimit n cs) → zipWith n f cs max-cs ≡ zipWith n g cs max-cs
  zipWith-cong n f≗g [] [] = refl
  zipWith-cong n f≗g (c ∷ cs) (max-c ∷ max-cs) = Eq.cong₂ _∷_ (f≗g c max-c) (zipWith-cong n f≗g cs max-cs)

  zipWith⇒map : {i : Size} → {D A Result : Set} → (n : ℕ≥ 2) → (f : (expr : CCC D i A) → Result) → (cs : List (CCC D i A)) → (max-cs : ListChoiceLengthLimit n cs) → zipWith n (λ e max-e → f e) cs max-cs ≡ List.map f cs
  zipWith⇒map n f [] [] = refl
  zipWith⇒map n f (c ∷ cs) (max-c ∷ max-cs) = Eq.cong₂ _∷_ refl (zipWith⇒map n f cs max-cs)


  conf : {D : Set} → (n : ℕ≥ 2) → CCCꟲ D → FCCꟲ n D
  conf (sucs n) config d = ℕ≥.cappedFin (config d)

  fnoc : {D : Set} → (n : ℕ≥ 2) → FCCꟲ n D → CCCꟲ D
  fnoc n config d = Fin.toℕ (config d)

  preserves-⊆ : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → (expr : CCC D i A) → (choiceLengthLimit : ChoiceLengthLimit n expr) → ⟦ translate n expr choiceLengthLimit ⟧ₙ ⊆[ fnoc n ] ⟦ expr ⟧ₐ
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

  preserves-⊇ : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → (expr : CCC D i A) → (choiceLengthLimit : ChoiceLengthLimit n {i} expr) → ⟦ expr ⟧ₐ ⊆[ conf n ] ⟦ translate n expr choiceLengthLimit ⟧ₙ
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

  preserves : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → (expr : CCC D i A) → (choiceLengthLimit : ChoiceLengthLimit n expr) → ⟦ translate n expr choiceLengthLimit ⟧ₙ ≅[ fnoc n ][ conf n ] ⟦ expr ⟧ₐ
  preserves n expr choiceLengthLimit = preserves-⊆ n expr choiceLengthLimit , preserves-⊇ n expr choiceLengthLimit

  -- Can't instantiate a LanguageCompiler because the expression compiler and the configuration compiler depend on the expression

  -- CCC→FCC : {i : Size} → {D : Set} → LanguageCompiler (CCCL D Variant Artifact∈ₛVariant {i}) (λ e → FCCL (maxChoiceLength e) D Variant Artifact∈ₛVariant)
  -- CCC→FCC n .LanguageCompiler.compile e = translate (maxChoiceLength e) e (maxChoiceLengthLimit e)
  -- CCC→FCC n .LanguageCompiler.config-compiler e .to = conf (maxChoiceLength e)
  -- CCC→FCC n .LanguageCompiler.config-compiler e .from = fnoc (maxChoiceLength e)
  -- CCC→FCC n .LanguageCompiler.preserves e = ≅[]-sym (preserves (maxChoiceLength e) e (maxChoiceLengthIsLimit e))


Fin→ℕ : {D : Set} → (n : ℕ≥ 2) -> IndexedDimension D n → D × ℕ
Fin→ℕ n (d , i) = (d , Fin.toℕ i)

Fin→ℕ⁻¹ : {D : Set} → (n : ℕ≥ 2) -> D × ℕ → IndexedDimension D n
Fin→ℕ⁻¹ n (d , i) = (d , ℕ≥.cappedFin {ℕ≥.pred n} i)

translate : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → (expr : CCC D i A) → FCC n (D × ℕ) ∞ A
translate n expr = FCC-map-dim n (Fin→ℕ (Exact.maxChoiceLength expr)) (FCC→FCC (Exact.maxChoiceLength expr) n (Exact.translate (Exact.maxChoiceLength expr) expr (Exact.maxChoiceLengthIsLimit expr)))

conf : {D : Set} → (n m : ℕ≥ 2) → CCCꟲ D → FCCꟲ n (D × ℕ)
conf n m = (_∘ Fin→ℕ⁻¹ m) ∘ FCCꟲ→FCCꟲ m n ∘ Exact.conf m

fnoc : {D : Set} → (n m : ℕ≥ 2) → FCCꟲ n (D × ℕ) → CCCꟲ D
fnoc n m = Exact.fnoc m ∘ FCCꟲ→FCCꟲ⁻¹ m n ∘ (_∘ Fin→ℕ m)

preserves : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → (expr : CCC D i A) → ⟦ translate n expr ⟧ₙ ≅[ fnoc n (Exact.maxChoiceLength expr) ][ conf n (Exact.maxChoiceLength expr) ] ⟦ expr ⟧ₐ
preserves n expr =
  ⟦ translate n expr ⟧ₙ
  ≅[]⟨⟩
  ⟦ FCC-map-dim n (Fin→ℕ (Exact.maxChoiceLength expr)) (FCC→FCC (Exact.maxChoiceLength expr) n (Exact.translate (Exact.maxChoiceLength expr) expr (Exact.maxChoiceLengthIsLimit expr))) ⟧ₙ
  ≅[]⟨ FCC-map-dim-preserves n (Fin→ℕ (Exact.maxChoiceLength expr)) (Fin→ℕ⁻¹ (Exact.maxChoiceLength expr)) (λ where (d , i) → Eq.cong₂ _,_ refl (lemma (Exact.maxChoiceLength expr) i)) (FCC→FCC (Exact.maxChoiceLength expr) n (Exact.translate (Exact.maxChoiceLength expr) expr (Exact.maxChoiceLengthIsLimit expr))) ⟩
  ⟦ FCC→FCC (Exact.maxChoiceLength expr) n (Exact.translate (Exact.maxChoiceLength expr) expr (Exact.maxChoiceLengthIsLimit expr)) ⟧ₙ
  ≅[]⟨ FCC→FCC-preserves (Exact.maxChoiceLength expr) n (Exact.translate (Exact.maxChoiceLength expr) expr (Exact.maxChoiceLengthIsLimit expr)) ⟩
  ⟦ Exact.translate (Exact.maxChoiceLength expr) expr (Exact.maxChoiceLengthIsLimit expr) ⟧ₙ
  ≅[]⟨ Exact.preserves (Exact.maxChoiceLength expr) expr (Exact.maxChoiceLengthIsLimit expr) ⟩
  ⟦ expr ⟧ₐ
  ≅[]-∎
  where
  lemma : (n : ℕ≥ 2) → (i : Fin (ℕ≥.toℕ (ℕ≥.pred n))) → ℕ≥.cappedFin {ℕ≥.pred n} (Fin.toℕ i) ≡ i
  lemma (sucs n) i = ℕ≥.cappedFin-toℕ i

-- Can't instantiate a LanguageCompiler because the configuration compiler depends on the expression

-- CCC→FCC : {i : Size} → {D : Set} → (n : ℕ≥ 2) → LanguageCompiler (CCCL D Variant Artifact∈ₛVariant {i}) (FCCL n (D × ℕ) Variant Artifact∈ₛVariant)
-- CCC→FCC n .LanguageCompiler.compile = translate n
-- CCC→FCC n .LanguageCompiler.config-compiler e .to = conf n (maxChoiceLength e)
-- CCC→FCC n .LanguageCompiler.config-compiler e .from = fnoc n (maxChoiceLength e)
-- CCC→FCC n .LanguageCompiler.preserves e = ≅[]-sym (preserves n e)
