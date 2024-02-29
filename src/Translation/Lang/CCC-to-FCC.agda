{-# OPTIONS --sized-types #-}
module Translation.Lang.CCC-to-FCC where

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
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; _≗_)
open import Relation.Nullary.Decidable using (yes; no)
open import Size using (Size; ↑_)
import Util.AuxProofs as ℕ
open import Util.List using (find-or-last; map-find-or-last; find-or-last⇒lookup; lookup⇒find-or-last)
open import Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs; _⊔_)
import Util.Vec as Vec

open Eq.≡-Reasoning using (step-≡; step-≡˘; _≡⟨⟩_; _∎)
open IndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-trans)
open IndexedSet.≅[]-Reasoning using (step-≅[]; _≅[]⟨⟩_; _≅[]-∎)
open IndexedSet.⊆-Reasoning using (step-⊆; _⊆-∎)

open import Lang.Choices

mutual
  data ListChoiceLengthLimit {D A : Set} (n : ℕ≥ 2) : {i : Size} → List (ArbitraryChoice D A {i}) → Set where
    [] : {i : Size} → ListChoiceLengthLimit n {i} []
    _∷_ : {i : Size} → {c : ArbitraryChoice D A {i}} → {cs : List (ArbitraryChoice D A {i})} → ChoiceLengthLimit n {i} c → ListChoiceLengthLimit n {i} cs → ListChoiceLengthLimit n {i} (c ∷ cs)

  data List⁺ChoiceLengthLimit {D A : Set} (n : ℕ≥ 2) : {i : Size} → List⁺ (ArbitraryChoice D A {i}) → Set where
    _∷_ : {i : Size} → {c : ArbitraryChoice D A {i}} → {cs : List (ArbitraryChoice D A {i})} → ChoiceLengthLimit n {i} c → ListChoiceLengthLimit n {i} cs → List⁺ChoiceLengthLimit n {i} (c ∷ cs)

  data ChoiceLengthLimit {D A : Set} (n : ℕ≥ 2) : {i : Size} → ArbitraryChoice D A {i} → Set where
    artifact : {i : Size} → {a : A} → {cs : List (ArbitraryChoice D A {i})} → ListChoiceLengthLimit n {i} cs → ChoiceLengthLimit n {↑ i} (artifact a cs)
    choice : {i : Size} → {d : D} → {cs : List⁺ (ArbitraryChoice D A {i})} → List⁺.length cs ≤ ℕ≥.toℕ n → List⁺ChoiceLengthLimit n {i} cs → ChoiceLengthLimit n {↑ i} (choice d cs)

mutual
  ListChoiceLengthLimit-⊔ : {D A : Set} → {cs : List (ArbitraryChoice D A)} → {n₁ n₂ : ℕ≥ 2} → ListChoiceLengthLimit n₁ cs → ListChoiceLengthLimit (n₁ ⊔ n₂) cs
  ListChoiceLengthLimit-⊔ [] = []
  ListChoiceLengthLimit-⊔ (c ∷ cs) = ChoiceLengthLimit-⊔ c ∷ ListChoiceLengthLimit-⊔ cs

  List⁺ChoiceLengthLimit-⊔ : {D A : Set} → {cs : List⁺ (ArbitraryChoice D A)} → {n₁ n₂ : ℕ≥ 2} → List⁺ChoiceLengthLimit n₁ cs → List⁺ChoiceLengthLimit (n₁ ⊔ n₂) cs
  List⁺ChoiceLengthLimit-⊔ (c ∷ cs) = ChoiceLengthLimit-⊔ c ∷ ListChoiceLengthLimit-⊔ cs

  ChoiceLengthLimit-⊔ : {D A : Set} → {cs : ArbitraryChoice D A} → {n₁ n₂ : ℕ≥ 2} → ChoiceLengthLimit n₁ cs → ChoiceLengthLimit (n₁ ⊔ n₂) cs
  ChoiceLengthLimit-⊔ (artifact max-cs) = artifact (ListChoiceLengthLimit-⊔ max-cs)
  ChoiceLengthLimit-⊔ {cs = choice d cs} {n₁ = n₁} {n₂ = n₂} (choice max-cs≤n max-cs) = choice (≤-trans (ℕ.m≤n⇒m≤n⊔o (ℕ≥.toℕ n₂) max-cs≤n) (≤-reflexive (Eq.sym (ℕ≥.toℕ-⊔ n₁ n₂)))) (List⁺ChoiceLengthLimit-⊔ max-cs)

-- calculcates the maximum + 2 to ensure that it is ≥ 2
maximum : List (ℕ≥ 2) → ℕ≥ 2
maximum [] = sucs zero
maximum (n ∷ ns) = n ⊔ maximum ns

maximum⁺ : List⁺ (ℕ≥ 2) → ℕ≥ 2
maximum⁺ (n ∷ ns) = maximum (n ∷ ns)

-- calculcates the maximum + 2 to ensure that it is ≥ 2
maxChoiceLength : {i : Size} → {D A : Set} → ArbitraryChoice D A {i} → ℕ≥ 2
maxChoiceLength (artifact a cs) = maximum (List.map maxChoiceLength cs)
maxChoiceLength (choice d cs) = sucs (List⁺.length cs) ⊔ maximum⁺ (List⁺.map maxChoiceLength cs)

ListChoiceLengthLimit-⊔-comm : {D A : Set} → {cs : List (ArbitraryChoice D A)} → {n m : ℕ≥ 2} → ListChoiceLengthLimit (n ⊔ m) cs → ListChoiceLengthLimit (m ⊔ n) cs
ListChoiceLengthLimit-⊔-comm {cs = cs} {n = n} {m = m} a = Eq.subst (λ e → ListChoiceLengthLimit e cs) (ℕ≥.⊔-comm n m) a

List⁺ChoiceLengthLimit-⊔-comm : {D A : Set} → {cs : List⁺ (ArbitraryChoice D A)} → {n m : ℕ≥ 2} → List⁺ChoiceLengthLimit (n ⊔ m) cs → List⁺ChoiceLengthLimit (m ⊔ n) cs
List⁺ChoiceLengthLimit-⊔-comm {cs = cs} {n = n} {m = m} a = Eq.subst (λ e → List⁺ChoiceLengthLimit e cs) (ℕ≥.⊔-comm n m) a

mutual
  maximumIsLimit : {D A : Set} → (cs : List (ArbitraryChoice D A)) → ListChoiceLengthLimit (maximum (List.map maxChoiceLength cs)) cs
  maximumIsLimit [] = []
  maximumIsLimit (c ∷ cs) = ChoiceLengthLimit-⊔ (maxChoiceLengthIsLimit c) ∷ ListChoiceLengthLimit-⊔-comm {m = maxChoiceLength c} (ListChoiceLengthLimit-⊔ (maximumIsLimit cs))

  maximum⁺IsLimit : {D A : Set} (cs : List⁺ (ArbitraryChoice D A)) → List⁺ChoiceLengthLimit (maximum⁺ (List⁺.map maxChoiceLength cs)) cs
  maximum⁺IsLimit (c ∷ cs) = ChoiceLengthLimit-⊔ (maxChoiceLengthIsLimit c) ∷ ListChoiceLengthLimit-⊔-comm {m = maxChoiceLength c} (ListChoiceLengthLimit-⊔ (maximumIsLimit cs))

  maxChoiceLengthIsLimit : {D A : Set} → (expr : ArbitraryChoice D A) → ChoiceLengthLimit (maxChoiceLength expr) expr
  maxChoiceLengthIsLimit (artifact a cs) = artifact (maximumIsLimit cs)
  maxChoiceLengthIsLimit (choice d cs) = choice (≤-trans (ℕ.m≤n⇒m≤n⊔o (ℕ≥.toℕ (maximum⁺ (List⁺.map maxChoiceLength cs))) (≤-trans (ℕ.n≤1+n (List⁺.length cs)) (ℕ.n≤1+n (suc (List⁺.length cs))))) (≤-reflexive (Eq.sym (ℕ≥.toℕ-⊔ (sucs (List⁺.length cs)) (maximum⁺ (List⁺.map maxChoiceLength cs)))))) (List⁺ChoiceLengthLimit-⊔-comm (List⁺ChoiceLengthLimit-⊔ (maximum⁺IsLimit cs)))

mutual
  ArbitraryChoice→NAryChoice : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → (expr : ArbitraryChoice D A {i}) → ChoiceLengthLimit n {i} expr → NAryChoice n D A
  ArbitraryChoice→NAryChoice n (artifact a cs) (artifact max-cs) = artifact a (zipWith n (ArbitraryChoice→NAryChoice n) cs max-cs)
  ArbitraryChoice→NAryChoice (sucs n) (choice d (c ∷ cs)) (choice max≤n (max-c ∷ max-cs)) =
    choice d (Vec.saturate max≤n (ArbitraryChoice→NAryChoice (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs))))

  -- Can probably be generalized
  zipWith : {i : Size} → {D A Result : Set} → (n : ℕ≥ 2) → ((expr : ArbitraryChoice D A {i}) → ChoiceLengthLimit n expr → Result) → (cs : List (ArbitraryChoice D A {i})) → ListChoiceLengthLimit n cs → List Result
  zipWith n f [] [] = []
  zipWith n f (c ∷ cs) (max-c ∷ max-cs) = f c max-c ∷ zipWith n f cs max-cs

  length-zipWith : {i : Size} → {D A Result : Set} → (n : ℕ≥ 2) → {f : (expr : ArbitraryChoice D A {i}) → ChoiceLengthLimit n expr → Result} → (cs : List (ArbitraryChoice D A {i})) → (max-cs : ListChoiceLengthLimit n cs) → List.length (zipWith {i} n f cs max-cs) ≡ List.length cs
  length-zipWith n [] [] = refl
  length-zipWith n (c ∷ cs) (max-c ∷ max-cs) = Eq.cong suc (length-zipWith n cs max-cs)

map∘zipWith : {i : Size} → {D A Result₁ Result₂ : Set} → (n : ℕ≥ 2) → {g : Result₁ → Result₂} → {f : (expr : ArbitraryChoice D A {i}) → ChoiceLengthLimit n expr → Result₁} → (cs : List (ArbitraryChoice D A {i})) → (max-cs : ListChoiceLengthLimit n cs) → List.map g (zipWith n f cs max-cs) ≡ zipWith n (λ e max-e → g (f e max-e)) cs max-cs
map∘zipWith n [] [] = refl
map∘zipWith n (c ∷ cs) (max-c ∷ max-cs) = Eq.cong₂ _∷_ refl (map∘zipWith n cs max-cs)

zipWith-cong : {i : Size} → {D A Result : Set} → (n : ℕ≥ 2) → {f g : (expr : ArbitraryChoice D A {i}) → ChoiceLengthLimit n expr → Result} → ((e : ArbitraryChoice D A {i}) → (max-e : ChoiceLengthLimit n e) → f e max-e ≡ g e max-e) → (cs : List (ArbitraryChoice D A {i})) → (max-cs : ListChoiceLengthLimit n cs) → zipWith n f cs max-cs ≡ zipWith n g cs max-cs
zipWith-cong n f≗g [] [] = refl
zipWith-cong n f≗g (c ∷ cs) (max-c ∷ max-cs) = Eq.cong₂ _∷_ (f≗g c max-c) (zipWith-cong n f≗g cs max-cs)

zipWith⇒map : {i : Size} → {D A Result : Set} → (n : ℕ≥ 2) → (f : (expr : ArbitraryChoice D A {i}) → Result) → (cs : List (ArbitraryChoice D A {i})) → (max-cs : ListChoiceLengthLimit n cs) → zipWith n (λ e max-e → f e) cs max-cs ≡ List.map f cs
zipWith⇒map n f [] [] = refl
zipWith⇒map n f (c ∷ cs) (max-c ∷ max-cs) = Eq.cong₂ _∷_ refl (zipWith⇒map n f cs max-cs)


ArbitraryChoiceConfig→NAryChoiceConfig : {D : Set} → (n : ℕ≥ 2) → ArbitraryChoiceConfig D → NAryChoiceConfig n D
ArbitraryChoiceConfig→NAryChoiceConfig (sucs n) config d = ℕ≥.cappedFin (config d)

ArbitraryChoiceConfig→NAryChoiceConfig⁻¹ : {D : Set} → (n : ℕ≥ 2) → NAryChoiceConfig n D → ArbitraryChoiceConfig D
ArbitraryChoiceConfig→NAryChoiceConfig⁻¹ n config d = Fin.toℕ (config d)

ArbitraryChoice→NAryChoice-preserves-⊆ : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → (expr : ArbitraryChoice D A {i}) → (choiceLengthLimit : ChoiceLengthLimit n expr) → ⟦ ArbitraryChoice→NAryChoice n expr choiceLengthLimit ⟧ₙ ⊆[ ArbitraryChoiceConfig→NAryChoiceConfig⁻¹ n ] ⟦ expr ⟧ₐ
ArbitraryChoice→NAryChoice-preserves-⊆ n (artifact a cs) (artifact max-cs) config =
  ⟦ ArbitraryChoice→NAryChoice n (artifact a cs) (artifact max-cs) ⟧ₙ config
  ≡⟨⟩
  ⟦ artifact a (zipWith n (ArbitraryChoice→NAryChoice n) cs max-cs) ⟧ₙ config
  ≡⟨⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₙ config) (zipWith n (ArbitraryChoice→NAryChoice n) cs max-cs))
  ≡⟨ Eq.cong₂ artifact refl (map∘zipWith n cs max-cs) ⟩
  artifact a (zipWith n (λ e max-e → ⟦ ArbitraryChoice→NAryChoice n e max-e ⟧ₙ config) cs max-cs)
  ≡⟨ Eq.cong₂ artifact refl (zipWith-cong n (λ e max-e → ArbitraryChoice→NAryChoice-preserves-⊆ n e max-e config) cs max-cs) ⟩
  artifact a (zipWith n (λ e max-e → ⟦ e ⟧ₐ (ArbitraryChoiceConfig→NAryChoiceConfig⁻¹ n config)) cs max-cs)
  ≡⟨ Eq.cong₂ artifact refl (zipWith⇒map n (λ e → ⟦ e ⟧ₐ (ArbitraryChoiceConfig→NAryChoiceConfig⁻¹ n config)) cs max-cs) ⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₐ (ArbitraryChoiceConfig→NAryChoiceConfig⁻¹ n config)) cs)
  ≡⟨⟩
  ⟦ artifact a cs ⟧ₐ (ArbitraryChoiceConfig→NAryChoiceConfig⁻¹ n config)
  ∎
ArbitraryChoice→NAryChoice-preserves-⊆ (sucs n) (choice d (c ∷ cs)) (choice max≤n (max-c ∷ max-cs)) config =
  ⟦ ArbitraryChoice→NAryChoice (sucs n) (choice d (c ∷ cs)) (choice (max≤n) (max-c ∷ max-cs)) ⟧ₙ config
  ≡⟨⟩
  ⟦ choice d (Vec.saturate max≤n (ArbitraryChoice→NAryChoice (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs)))) ⟧ₙ config
  ≡⟨⟩
  ⟦ Vec.lookup (Vec.saturate max≤n (ArbitraryChoice→NAryChoice (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs)))) (config d) ⟧ₙ config
  ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Vec.lookup-saturate max≤n (ArbitraryChoice→NAryChoice (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs))) (config d)) refl ⟩
  ⟦ Vec.lookup (ArbitraryChoice→NAryChoice (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs))) (ℕ≥.cappedFin (Fin.toℕ (config d))) ⟧ₙ config
  ≡⟨⟩
  ⟦ Vec.lookup (Vec.cast (Eq.cong suc (length-zipWith (sucs n) cs max-cs)) (ArbitraryChoice→NAryChoice (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs))) (ℕ≥.cappedFin (Fin.toℕ (config d))) ⟧ₙ config
  ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Vec.lookup-cast₁ (Eq.cong suc (length-zipWith (sucs n) cs max-cs)) (ArbitraryChoice→NAryChoice (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs)) (ℕ≥.cappedFin (Fin.toℕ (config d)))) refl ⟩
  ⟦ Vec.lookup (ArbitraryChoice→NAryChoice (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs)) (Fin.cast (Eq.sym (Eq.cong suc (length-zipWith (sucs n) cs max-cs))) (ℕ≥.cappedFin (Fin.toℕ (config d)))) ⟧ₙ config
  ≡⟨ Eq.cong₂ ⟦_⟧ₙ (Eq.cong₂ Vec.lookup (refl {x = ArbitraryChoice→NAryChoice (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs)}) (ℕ≥.cast-cappedFin (Fin.toℕ (config d)) (Eq.sym (Eq.cong suc (length-zipWith (sucs n) cs max-cs))))) refl ⟩
  ⟦ Vec.lookup (ArbitraryChoice→NAryChoice (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs)) (ℕ≥.cappedFin (Fin.toℕ (config d))) ⟧ₙ config
  ≡˘⟨ Eq.cong₂ ⟦_⟧ₙ (find-or-last⇒lookup (ArbitraryChoice→NAryChoice (sucs n) c max-c) (zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs)) refl ⟩
  ⟦ find-or-last (Fin.toℕ (config d)) (ArbitraryChoice→NAryChoice (sucs n) c max-c ∷ zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs) ⟧ₙ config
  ≡⟨ map-find-or-last (λ e → ⟦ e ⟧ₙ config) (Fin.toℕ (config d)) (ArbitraryChoice→NAryChoice (sucs n) c max-c ∷ zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs) ⟩
  find-or-last (Fin.toℕ (config d)) (⟦ ArbitraryChoice→NAryChoice (sucs n) c max-c ⟧ₙ config ∷ List.map (λ e → ⟦ e ⟧ₙ config) (zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs))
  ≡⟨ Eq.cong₂ find-or-last refl (Eq.cong₂ _∷_ refl (map∘zipWith (sucs n) cs max-cs)) ⟩
  find-or-last (Fin.toℕ (config d)) (⟦ ArbitraryChoice→NAryChoice (sucs n) c max-c ⟧ₙ config ∷ zipWith (sucs n) (λ e max-e → ⟦ ArbitraryChoice→NAryChoice (sucs n) e max-e ⟧ₙ config) cs max-cs)
  ≡⟨ Eq.cong₂ find-or-last refl (Eq.cong₂ _∷_ (ArbitraryChoice→NAryChoice-preserves-⊆ (sucs n) c max-c config) (zipWith-cong (sucs n) (λ e max-e → ArbitraryChoice→NAryChoice-preserves-⊆ (sucs n) e max-e config) cs max-cs)) ⟩
  find-or-last (Fin.toℕ (config d)) (⟦ c ⟧ₐ (ArbitraryChoiceConfig→NAryChoiceConfig⁻¹ (sucs n) config) ∷ zipWith (sucs n) (λ e max-e → ⟦ e ⟧ₐ (ArbitraryChoiceConfig→NAryChoiceConfig⁻¹ (sucs n) config)) cs max-cs)
  ≡⟨ Eq.cong₂ find-or-last refl (Eq.cong₂ _∷_ refl (zipWith⇒map (sucs n) (λ e → ⟦ e ⟧ₐ (ArbitraryChoiceConfig→NAryChoiceConfig⁻¹ (sucs n) config)) cs max-cs)) ⟩
  find-or-last (Fin.toℕ (config d)) (⟦ c ⟧ₐ (ArbitraryChoiceConfig→NAryChoiceConfig⁻¹ (sucs n) config) ∷ List.map (λ e → ⟦ e ⟧ₐ (ArbitraryChoiceConfig→NAryChoiceConfig⁻¹ (sucs n) config)) cs)
  ≡⟨⟩
  find-or-last (Fin.toℕ (config d)) (List⁺.map (λ e → ⟦ e ⟧ₐ (ArbitraryChoiceConfig→NAryChoiceConfig⁻¹ (sucs n) config)) (c ∷ cs))
  ≡˘⟨ map-find-or-last (λ e → ⟦ e ⟧ₐ (ArbitraryChoiceConfig→NAryChoiceConfig⁻¹ (sucs n) config)) (ArbitraryChoiceConfig→NAryChoiceConfig⁻¹ (sucs n) config d) (c ∷ cs) ⟩
  ⟦ find-or-last (ArbitraryChoiceConfig→NAryChoiceConfig⁻¹ (sucs n) config d) (c ∷ cs) ⟧ₐ (ArbitraryChoiceConfig→NAryChoiceConfig⁻¹ (sucs n) config)
  ≡⟨⟩
  ⟦ choice d (c ∷ cs) ⟧ₐ (ArbitraryChoiceConfig→NAryChoiceConfig⁻¹ (sucs n) config)
  ∎

ArbitraryChoice→NAryChoice-preserves-⊇ : {i : Size} → {D A : Set} → (n : ℕ≥ 2) → (expr : ArbitraryChoice D A {i}) → (choiceLengthLimit : ChoiceLengthLimit n {i} expr) → ⟦ expr ⟧ₐ ⊆[ ArbitraryChoiceConfig→NAryChoiceConfig n ] ⟦ ArbitraryChoice→NAryChoice n expr choiceLengthLimit ⟧ₙ
ArbitraryChoice→NAryChoice-preserves-⊇ n (artifact a cs) (artifact max-cs) config =
  ⟦ artifact a cs ⟧ₐ config
  ≡⟨⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₐ config) cs)
  ≡˘⟨ Eq.cong₂ artifact refl (zipWith⇒map n (λ e → ⟦ e ⟧ₐ config) cs max-cs) ⟩
  artifact a (zipWith n (λ e max-e → ⟦ e ⟧ₐ config) cs max-cs)
  ≡⟨ Eq.cong₂ artifact refl (zipWith-cong n (λ e max-e → ArbitraryChoice→NAryChoice-preserves-⊇ n e max-e config) cs max-cs) ⟩
  artifact a (zipWith n (λ e max-e → ⟦ ArbitraryChoice→NAryChoice n e max-e ⟧ₙ (ArbitraryChoiceConfig→NAryChoiceConfig n config)) cs max-cs)
  ≡˘⟨ Eq.cong₂ artifact refl (map∘zipWith n cs max-cs) ⟩
  artifact a (List.map (λ e → ⟦ e ⟧ₙ (ArbitraryChoiceConfig→NAryChoiceConfig n config)) (zipWith n (ArbitraryChoice→NAryChoice n) cs max-cs))
  ≡⟨⟩
  ⟦ artifact a (zipWith n (ArbitraryChoice→NAryChoice n) cs max-cs) ⟧ₙ (ArbitraryChoiceConfig→NAryChoiceConfig n config)
  ≡⟨⟩
  ⟦ ArbitraryChoice→NAryChoice n (artifact a cs) (artifact max-cs) ⟧ₙ (ArbitraryChoiceConfig→NAryChoiceConfig n config)
  ∎
ArbitraryChoice→NAryChoice-preserves-⊇ (sucs n) (choice d (c ∷ cs)) (choice (s≤s max≤n) (max-c ∷ max-cs)) config =
  ⟦ choice d (c ∷ cs) ⟧ₐ config
  ≡⟨⟩
  ⟦ find-or-last (config d) (c ∷ cs) ⟧ₐ config
  ≡⟨ map-find-or-last (λ e → ⟦ e ⟧ₐ config) (config d) (c ∷ cs) ⟩
  find-or-last (config d) (List⁺.map (λ e → ⟦ e ⟧ₐ config) (c ∷ cs))
  ≡⟨⟩
  find-or-last (config d) (⟦ c ⟧ₐ config ∷ List.map (λ e → ⟦ e ⟧ₐ config) cs)
  ≡˘⟨ Eq.cong₂ find-or-last refl (Eq.cong₂ _∷_ refl (zipWith⇒map (sucs n) (λ e → ⟦ e ⟧ₐ config) cs max-cs)) ⟩
  find-or-last (config d) (⟦ c ⟧ₐ config ∷ zipWith (sucs n) (λ e max-e → ⟦ e ⟧ₐ config) cs max-cs)
  ≡⟨ Eq.cong₂ find-or-last refl (Eq.cong₂ _∷_ (ArbitraryChoice→NAryChoice-preserves-⊇ (sucs n) c max-c config) (zipWith-cong (sucs n) (λ e max-e → ArbitraryChoice→NAryChoice-preserves-⊇ (sucs n) e max-e config) cs max-cs)) ⟩
  find-or-last (config d) (⟦ ArbitraryChoice→NAryChoice (sucs n) c max-c ⟧ₙ (ArbitraryChoiceConfig→NAryChoiceConfig (sucs n) config) ∷ zipWith (sucs n) (λ e max-e → ⟦ ArbitraryChoice→NAryChoice (sucs n) e max-e ⟧ₙ (ArbitraryChoiceConfig→NAryChoiceConfig (sucs n) config)) cs max-cs)
  ≡˘⟨ Eq.cong₂ find-or-last refl (Eq.cong₂ _∷_ refl (map∘zipWith (sucs n) cs max-cs)) ⟩
  find-or-last (config d) (⟦ ArbitraryChoice→NAryChoice (sucs n) c max-c ⟧ₙ (ArbitraryChoiceConfig→NAryChoiceConfig (sucs n) config) ∷ List.map (λ e → ⟦ e ⟧ₙ (ArbitraryChoiceConfig→NAryChoiceConfig (sucs n) config)) (zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs))
  ≡˘⟨ map-find-or-last (λ e → ⟦ e ⟧ₙ (ArbitraryChoiceConfig→NAryChoiceConfig (sucs n) config)) (config d) (ArbitraryChoice→NAryChoice (sucs n) c max-c ∷ zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs) ⟩
  ⟦ find-or-last (config d) (ArbitraryChoice→NAryChoice (sucs n) c max-c ∷ zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs) ⟧ₙ (ArbitraryChoiceConfig→NAryChoiceConfig (sucs n) config)
  ≡⟨ Eq.cong₂ ⟦_⟧ₙ (find-or-last⇒lookup (ArbitraryChoice→NAryChoice (sucs n) c max-c) (zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs)) refl ⟩
  ⟦ Vec.lookup (ArbitraryChoice→NAryChoice (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs)) (ℕ≥.cappedFin (config d)) ⟧ₙ (ArbitraryChoiceConfig→NAryChoiceConfig (sucs n) config)
  ≡˘⟨ Eq.cong₂ ⟦_⟧ₙ (Eq.cong₂ Vec.lookup (refl {x = ArbitraryChoice→NAryChoice (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs)}) (ℕ≥.cast-cappedFin (config d) (Eq.sym (Eq.cong suc (length-zipWith (sucs n) cs max-cs))))) refl ⟩
  ⟦ Vec.lookup (ArbitraryChoice→NAryChoice (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs)) (Fin.cast (Eq.sym (Eq.cong suc (length-zipWith (sucs n) cs max-cs))) (ℕ≥.cappedFin (config d))) ⟧ₙ (ArbitraryChoiceConfig→NAryChoiceConfig (sucs n) config)
  ≡˘⟨ Eq.cong₂ ⟦_⟧ₙ (Vec.lookup-cast₁ (Eq.cong suc (length-zipWith (sucs n) cs max-cs)) (ArbitraryChoice→NAryChoice (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs)) (ℕ≥.cappedFin (config d))) refl ⟩
  ⟦ Vec.lookup (Vec.cast (Eq.cong suc (length-zipWith (sucs n) cs max-cs)) (ArbitraryChoice→NAryChoice (sucs n) c max-c ∷ Vec.fromList (zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs))) (ℕ≥.cappedFin (config d)) ⟧ₙ (ArbitraryChoiceConfig→NAryChoiceConfig (sucs n) config)
  ≡⟨⟩
  ⟦ Vec.lookup (ArbitraryChoice→NAryChoice (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs))) (ℕ≥.cappedFin (config d)) ⟧ₙ (ArbitraryChoiceConfig→NAryChoiceConfig (sucs n) config)
  ≡˘⟨ Eq.cong₂ ⟦_⟧ₙ (Eq.cong₂ Vec.lookup (refl {x = ArbitraryChoice→NAryChoice (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs))}) (ℕ≥.cappedFin-idempotent max≤n (config d))) refl ⟩
  ⟦ Vec.lookup (ArbitraryChoice→NAryChoice (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs))) (ℕ≥.cappedFin (Fin.toℕ (ArbitraryChoiceConfig→NAryChoiceConfig (sucs n) config d))) ⟧ₙ (ArbitraryChoiceConfig→NAryChoiceConfig (sucs n) config)
  ≡˘⟨ Eq.cong₂ ⟦_⟧ₙ (Vec.lookup-saturate (s≤s max≤n) (ArbitraryChoice→NAryChoice (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs))) (ArbitraryChoiceConfig→NAryChoiceConfig (sucs n) config d)) refl ⟩
  ⟦ Vec.lookup (Vec.saturate (s≤s max≤n) (ArbitraryChoice→NAryChoice (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs)))) (ArbitraryChoiceConfig→NAryChoiceConfig (sucs n) config d) ⟧ₙ (ArbitraryChoiceConfig→NAryChoiceConfig (sucs n) config)
  ≡⟨⟩
  ⟦ choice d (Vec.saturate (s≤s max≤n) (ArbitraryChoice→NAryChoice (sucs n) c max-c ∷ Vec.cast (length-zipWith (sucs n) cs max-cs) (Vec.fromList (zipWith (sucs n) (ArbitraryChoice→NAryChoice (sucs n)) cs max-cs)))) ⟧ₙ (ArbitraryChoiceConfig→NAryChoiceConfig (sucs n) config)
  ≡⟨⟩
  ⟦ ArbitraryChoice→NAryChoice (sucs n) (choice d (c ∷ cs)) (choice (s≤s max≤n) (max-c ∷ max-cs)) ⟧ₙ (ArbitraryChoiceConfig→NAryChoiceConfig (sucs n) config)
  ∎

ArbitraryChoice→NAryChoice-preserves : {D A : Set} → (n : ℕ≥ 2) → (expr : ArbitraryChoice D A) → (choiceLengthLimit : ChoiceLengthLimit n expr) → ⟦ ArbitraryChoice→NAryChoice n expr choiceLengthLimit ⟧ₙ ≅[ ArbitraryChoiceConfig→NAryChoiceConfig⁻¹ n ][ ArbitraryChoiceConfig→NAryChoiceConfig n ] ⟦ expr ⟧ₐ
ArbitraryChoice→NAryChoice-preserves n expr choiceLengthLimit = ArbitraryChoice→NAryChoice-preserves-⊆ n expr choiceLengthLimit , ArbitraryChoice→NAryChoice-preserves-⊇ n expr choiceLengthLimit
