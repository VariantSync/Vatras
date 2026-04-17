open import Data.Nat as ℕ using (ℕ; suc; zero; _≤_; _<_; z≤n; s≤s; _>_; _+_; _∸_; _*_; _^_; _≟_)
open import Data.Product as Prod using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
open import Function using (_∘_; _∘′_; const; id)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; _≢_; refl)
open import Vatras.Framework.Definitions using (𝔸; 𝔽; NAT; atomSize)

module Vatras.Succinctness.Relations.2CC≰FST
  (F : 𝔽)
  (f : ℕ → F)
  (_==_ : DecidableEquality F)
  (f-injective : ∀ {i j : ℕ} → i ≢ j → f i ≢ f j)
  (diagonalization : F × ℕ → F)
  (diagonalization⁻¹ : F → F × ℕ)
  (diagonalization-injective : diagonalization⁻¹ ∘ diagonalization ≗ id)
  where

open import Data.Bool as Bool using (Bool; true; false; _∨_; if_then_else_)
import Data.Bool.Properties as Bool
open import Data.Empty using (⊥-elim)
import Data.Nat.Properties as ℕ
open import Data.Fin as Fin using (Fin; zero; suc)
import Data.Fin.Properties as Fin
open import Data.List as List using (List; []; _∷_; _++_)
import Data.List.Properties as List
import Data.List.Membership.Propositional as List
open import Data.List.Relation.Binary.Sublist.Propositional as Sublist using ([]; _∷_; _∷ʳ_)
import Data.List.Relation.Binary.Subset.Propositional as Subset
import Data.List.Relation.Binary.Subset.Propositional.Properties as Subset
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Unary.AllPairs as AllPairs using (AllPairs; []; _∷_)
import Data.List.Relation.Unary.AllPairs.Properties as AllPairs
import Data.List.Relation.Unary.Unique.Propositional as List
import Data.List.Relation.Unary.Unique.Propositional.Properties as Unique
import Data.Product.Properties as Prod
open import Data.Unit using (tt)
open import Function.Bundles using (Equivalence)
open import Relation.Nullary.Decidable using (Dec; does; yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Relation.Unary using (Decidable)
open import Size using (Size; ∞)

open import Vatras.Util.AuxProofs using (true≢false; does≡true; does≡false)
open import Vatras.Data.EqIndexedSet using (_⊆_; ⊆-trans; _∈_)
open import Vatras.Framework.Variants using (Rose; Rose-injective)
import Vatras.Util.List as List
open import Vatras.Lang.All.Fixed F (Rose ∞)
import Vatras.Lang.2CC.ReflectsVariantSize as 2CC
import Vatras.Translation.LanguageMap
open Vatras.Translation.LanguageMap.Expressiveness diagonalization diagonalization⁻¹ diagonalization-injective using (2CC≽FST)
open import Vatras.Succinctness.ProofDefinition (Rose ∞) using (_≰ₛ_)
open import Vatras.Succinctness.Sizes using (sizeRose; Sized2CC; size2CC; SizedFST; sizeFST; size2CC>0)

open FST.Impose NAT hiding (_∈_; _==_)
open import Vatras.Lang.FST.Composition F NAT using (⊛-all-unique)
open import Vatras.Lang.FST.Util F NAT using (select≗filter)
open import Vatras.Lang.2CC.FixedArtifactLength F NAT using (different-children-counts) renaming (_≉_ to _≉'_)

artifact : ℕ → ℕ → FSTA ∞
artifact n zero = (0 , 2 ^ n) Rose.-< [] >-
artifact n (suc i) = (suc i , 0) Rose.-< [] >-

artifact-wf : (n i : ℕ) → WellFormed (artifact n i)
artifact-wf n zero = [] , []
artifact-wf n (suc i) = [] , []

feature : ℕ → ℕ → FSF
feature n i = (artifact n i ∷ []) ⊚ ([] ∷ [] , artifact-wf n i ∷ [])

fst : ℕ → SPL
fst n = (0 , 0) ◀ List.applyUpTo (λ i → f i :: feature n i) (suc n)

size-fst :
  ∀ (n : ℕ)
  → sizeFST (fst n) ≡ 3 + 2 ^ n + 2 * n
size-fst n =
  begin
    sizeFST (fst n)
  ≡⟨⟩
    1 + List.sum (List.map (suc ∘ List.sum ∘ List.map sizeRose ∘ FST.Impose.trees ∘ FST.Impose.impl) (List.applyUpTo (λ i → f i :: feature n i) (suc n)))
  ≡⟨⟩
    2 + (sizeRose (artifact n zero) + 0) + List.sum (List.map (suc ∘ List.sum ∘ List.map sizeRose ∘ FST.Impose.trees ∘ FST.Impose.impl) (List.applyUpTo (λ i → f (suc i) :: feature n (suc i)) n))
  ≡⟨ Eq.cong (λ x → 2 + (sizeRose (artifact n zero) + 0 + List.sum (List.map (suc ∘ List.sum ∘ List.map sizeRose ∘ FST.Impose.trees ∘ FST.Impose.impl) x))) (List.map-upTo (λ i → f (suc i) :: feature n (suc i)) n) ⟨
    2 + (sizeRose (artifact n zero) + 0) + List.sum (List.map (suc ∘ List.sum ∘ List.map sizeRose ∘ FST.Impose.trees ∘ FST.Impose.impl) (List.map (λ i → f (suc i) :: feature n (suc i)) (List.upTo n)))
  ≡⟨ Eq.cong (λ x → 2 + (sizeRose (artifact n zero) + 0) + List.sum x) (List.map-∘ (List.upTo n)) ⟨
    2 + (sizeRose (artifact n zero) + 0) + List.sum (List.map (λ i → suc (sizeRose (artifact n (suc i)) + 0)) (List.upTo n))
  ≡⟨⟩
    3 + (2 ^ n + 0 + 0) + List.sum (List.map (const 2) (List.upTo n))
  ≡⟨ Eq.cong (λ x → 3 + x + List.sum (List.map (const 2) (List.upTo n))) (ℕ.+-identityʳ (2 ^ n + 0)) ⟩
    3 + (2 ^ n + 0) + List.sum (List.map (const 2) (List.upTo n))
  ≡⟨ Eq.cong (λ x → 3 + x + List.sum (List.map (const 2) (List.upTo n))) (ℕ.+-identityʳ (2 ^ n)) ⟩
    3 + 2 ^ n + List.sum (List.map (const 2) (List.upTo n))
  ≡⟨ Eq.cong (λ x → 3 + 2 ^ n + List.sum x) (List.map-const 2 (List.upTo n)) ⟩
    3 + 2 ^ n + List.sum (List.replicate (List.length (List.upTo n)) 2)
  ≡⟨ Eq.cong (λ x → 3 + 2 ^ n + List.sum (List.replicate x 2)) (List.length-upTo n) ⟩
    3 + 2 ^ n + List.sum (List.replicate n 2)
  ≡⟨ Eq.cong (λ x → 3 + 2 ^ n + x) (List.sum-replicate n 2) ⟩
    3 + 2 ^ n + n * 2
  ≡⟨ Eq.cong (3 + 2 ^ n +_) (ℕ.*-comm n 2) ⟩
    3 + 2 ^ n + 2 * n
  ∎
  where
  open Eq.≡-Reasoning

variant : ℕ → ℕ → FSTA ∞
variant n i = (0 , 0) Rose.-< List.applyUpTo (artifact n) (suc i) >-

size-variant
  : (n i : ℕ)
  → 2 ^ n ≤ sizeRose (variant n i)
size-variant n i =
  begin
    2 ^ n
  ≡⟨ ℕ.+-identityʳ (2 ^ n) ⟨
    2 ^ n + 0
  <⟨ ℕ.m<n+m (2 ^ n + 0) {2} (s≤s z≤n) ⟩
    2 + (2 ^ n + 0)
  ≤⟨ ℕ.m≤m+n (2 + (2 ^ n + 0)) _ ⟩
    2 + (2 ^ n + 0) + List.sum (List.map sizeRose (List.applyUpTo (artifact n ∘ suc) i))
  ≡⟨⟩
    1 + sizeRose (artifact n zero) + List.sum (List.map sizeRose (List.applyUpTo (artifact n ∘ suc) i))
  ≡⟨⟩
    sizeRose (variant n i)
  ∎
  where
  open ℕ.≤-Reasoning

variant-≉ : ∀ n {l₁} {l₂} → l₁ ≢ l₂ → variant n l₁ ≉' variant n l₂
variant-≉ n {l₁} {l₂} l₁≢l₂ v₁≡v₂ = l₁≢l₂ (
    l₁
  ≡⟨ List.length-applyUpTo (artifact n ∘ suc) l₁ ⟨
    List.length (List.applyUpTo (artifact n ∘ suc) l₁)
  ≡⟨ ℕ.suc-injective v₁≡v₂ ⟩
    List.length (List.applyUpTo (artifact n ∘ suc) l₂)
  ≡⟨ List.length-applyUpTo (artifact n ∘ suc) l₂ ⟩
    l₂
  ∎)
  where
  open Eq.≡-Reasoning

fst-config : ℕ → FST.Configuration
fst-config i f' = List.any (λ k → does (f k == f')) (List.upTo (suc i))
-- f' ℕ.≤ᵇ i

select-applyUpTo-feature :
  ∀ (k n i : ℕ)
  → i ≤ n
  → select (fst-config i) (List.applyUpTo (λ m → f m :: feature k m) (suc n))
  ≡ List.applyUpTo (feature k) (suc i)
select-applyUpTo-feature k n i i≤n =
    select (fst-config i) (List.applyUpTo (λ m → f m :: feature k m) (suc n))
  ≡⟨ select≗filter (fst-config i) (List.applyUpTo (λ m → f m :: feature k m) (suc n)) ⟩
    List.map impl (List.filter P? (List.applyUpTo (λ m → f m :: feature k m) (suc n)))
  ≡⟨ Eq.cong (λ x → List.map impl (List.filterᵇ (fst-config i ∘ name) (List.applyUpTo (λ m → f m :: feature k m) (suc x)))) (ℕ.m+[n∸m]≡n i≤n) ⟨
    List.map impl (List.filter P? (List.applyUpTo (λ m → f m :: feature k m) (suc i + (n ∸ i))))
  ≡⟨ Eq.cong (λ x → List.map impl (List.filterᵇ (fst-config i ∘ name) x)) (List.applyUpTo-++⁺ (λ m → f m :: feature k m) (suc i) (n ∸ i)) ⟩
    List.map impl (List.filter P?
      (  List.applyUpTo (λ m → f m :: feature k m) (suc i)
      ++ List.applyUpTo (λ m → f (suc i + m) :: feature k (suc i + m)) (n ∸ i)))
  ≡⟨ Eq.cong (List.map impl) (List.filter-++ (Bool.T? ∘ fst-config i ∘ name)
      (List.applyUpTo (λ m → f m :: feature k m) (suc i))
      (List.applyUpTo (λ m → f (suc i + m) :: feature k (suc i + m)) (n ∸ i)) )
  ⟩
    List.map impl
      (  List.filter P? (List.applyUpTo (λ m → f m :: feature k m) (suc i))
      ++ List.filter P? (List.applyUpTo (λ m → f (suc i + m) :: feature k (suc i + m)) (n ∸ i)))
  ≡⟨ Eq.cong (List.map impl) (Eq.cong₂ _++_
      (List.filter-all P?
        (All.applyUpTo⁺₁ (λ m → f m :: feature k m) (suc i) P-true))
      (List.filter-none P?
        (All.applyUpTo⁺₂ (λ m → f (suc i + m) :: feature k (suc i + m)) (n ∸ i) P-false)))
  ⟩
    List.map impl (List.applyUpTo (λ m → f m :: feature k m) (suc i) ++ [])
  ≡⟨ Eq.cong (List.map impl) (List.++-identityʳ (List.applyUpTo (λ m → f m :: feature k m) (suc i))) ⟩
    List.map impl (List.applyUpTo (λ m → f m :: feature k m) (suc i))
  ≡⟨ List.map-applyUpTo (λ m → f m :: feature k m) impl (suc i) ⟩
    List.applyUpTo (feature k) (suc i)
  ∎
  where
  open Eq.≡-Reasoning

  P : (f : Feature) → Set
  P = Bool.T ∘ fst-config i ∘ name

  P? : Decidable P
  P? = Bool.T? ∘ fst-config i ∘ name

  P-true : {j : ℕ} → j < suc i → P (f j :: feature k j)
  P-true {j} (s≤s j≤i) = Equivalence.from Bool.T-≡ (go (suc i) zero z≤n (s≤s j≤i))
    where
    go : ∀ i k → k ≤ j → j < k + i → List.any (λ k → does (f k == f j)) (List.applyUpTo (k +_) i) ≡ true
    go zero k k≤j j<k+i = ⊥-elim (ℕ.≤⇒≯ k≤j (ℕ.≤-trans j<k+i (ℕ.≤-reflexive (ℕ.+-identityʳ k))))
    go (suc i) k k≤j j<k+i with k ≟ j
    go (suc i) k k≤j j<k+i | yes k≡j =
        List.any (λ k → does (f k == f j)) (List.applyUpTo (k +_) (suc i))
      ≡⟨⟩
        does (f (k + zero) == f j) ∨ List.any (λ k → does (f k == f j)) (List.applyUpTo (λ m → k + suc m) i)
      ≡⟨ Eq.cong (λ x → does (f x == f j) ∨ List.any (λ k → does (f k == f j)) (List.applyUpTo (λ m → k + suc m) i)) (ℕ.+-identityʳ k) ⟩
        does (f k == f j) ∨ List.any (λ k → does (f k == f j)) (List.applyUpTo (λ m → k + suc m) i)
      ≡⟨ Eq.cong (_∨ List.any (λ k → does (f k == f j)) (List.applyUpTo (λ m → k + suc m) i)) (does≡true (f k == f j) (Eq.cong f k≡j)) ⟩
        true ∨ List.any (λ k → does (f k == f j)) (List.applyUpTo (λ m → k + suc m) i)
      ≡⟨⟩
        true
      ∎
    go (suc i) k k≤j j<k+i | no k≢j =
        List.any (λ k → does (f k == f j)) (List.applyUpTo (k +_) (suc i))
      ≡⟨⟩
        does (f (k + zero) == f j) ∨ List.any (λ k → does (f k == f j)) (List.applyUpTo (λ m → k + suc m) i)
      ≡⟨ Eq.cong (λ x → does (f x == f j) ∨ List.any (λ k → does (f k == f j)) (List.applyUpTo (λ m → k + suc m) i)) (ℕ.+-identityʳ k) ⟩
        does (f k == f j) ∨ List.any (λ k → does (f k == f j)) (List.applyUpTo (λ m → k + suc m) i)
      ≡⟨ Eq.cong (_∨ List.any (λ k → does (f k == f j)) (List.applyUpTo (λ m → k + suc m) i)) (does≡false (f k == f j) (f-injective k≢j)) ⟩
        false ∨ List.any (λ k → does (f k == f j)) (List.applyUpTo (λ m → k + suc m) i)
      ≡⟨⟩
        List.any (λ k → does (f k == f j)) (List.applyUpTo (λ m → k + suc m) i)
      ≡⟨ Eq.cong (λ x → List.any (λ k → does (f k == f j)) x) (List.applyUpTo-cong (λ m → ℕ.+-suc k m) i) ⟩
        List.any (λ k → does (f k == f j)) (List.applyUpTo (λ m → suc k + m) i)
      ≡⟨ go i (suc k) (ℕ.≤∧≢⇒< k≤j k≢j) (ℕ.≤-trans j<k+i (ℕ.≤-reflexive (ℕ.+-suc k i))) ⟩
        true
      ∎

  P-false : (j : ℕ) → ¬ P (f (suc i + j) :: feature k (suc i + j))
  P-false j p = true≢false (Equivalence.to Bool.T-≡ p) (go (suc i) (suc i + j) zero (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-identityʳ (suc i))) (ℕ.m≤m+n (suc i) j)))
    where
    go : ∀ i m k → i + k ≤ m → List.any (λ k → does (f k == f m)) (List.applyUpTo (k +_) i) ≡ false
    go zero m k k≤j = refl
    go (suc i) m k k≤j =
        List.any (λ k → does (f k == f m)) (List.applyUpTo (k +_) (suc i))
      ≡⟨⟩
        does (f (k + zero) == f m) ∨ List.any (λ k → does (f k == f m)) (List.applyUpTo (λ m → k + suc m) i)
      ≡⟨ Eq.cong (λ x → does (f x == f m) ∨ List.any (λ k → does (f k == f m)) (List.applyUpTo (λ m → k + suc m) i)) (ℕ.+-identityʳ k) ⟩
        does (f k == f m) ∨ List.any (λ k → does (f k == f m)) (List.applyUpTo (λ m → k + suc m) i)
      ≡⟨ Eq.cong (_∨ List.any (λ k → does (f k == f m)) (List.applyUpTo (λ m → k + suc m) i)) (does≡false (f k == f m) (f-injective (ℕ.<⇒≢ (ℕ.≤-<-trans (ℕ.m≤n+m k i) (ℕ.<-≤-trans (ℕ.n<1+n (i + k)) k≤j))))) ⟩
        false ∨ List.any (λ k → does (f k == f m)) (List.applyUpTo (λ m → k + suc m) i)
      ≡⟨⟩
        List.any (λ k → does (f k == f m)) (List.applyUpTo (λ m → k + suc m) i)
      ≡⟨ Eq.cong (λ x → List.any (λ k → does (f k == f m)) x) (List.applyUpTo-cong (λ m → ℕ.+-suc k m) i) ⟩
        List.any (λ k → does (f k == f m)) (List.applyUpTo (λ m → suc k + m) i)
      ≡⟨ go i m (suc k) (ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-suc i k)) k≤j) ⟩
        false
      ∎

unique-variant : ∀ n m i → Unique (List.concatMap forget-uniqueness (List.applyUpTo (λ k → feature n (m + k)) i))
unique-variant n m zero = []
unique-variant n m (suc i) =
  go i m ℕ.≤-refl
  ∷ Eq.subst
    (λ x → Unique (List.concatMap forget-uniqueness x))
    (List.applyUpTo-cong (λ k → Eq.cong (feature n) (Eq.sym (ℕ.+-suc m k))) i)
    (unique-variant n (suc m) i)
  where
  artifacts-≉ : ∀ {i} {j} → i ≢ j → artifact n i ≉ artifact n j
  artifacts-≉ {zero} {zero} i≢j refl = i≢j refl
  artifacts-≉ {suc i} {suc j} i≢j refl = i≢j refl

  go : ∀ i' m' → m ≤ m' → All (_≉_ (artifact n (m + zero))) (List.concatMap forget-uniqueness (List.applyUpTo (λ k → feature n (m' + suc k)) i'))
  go zero m' m≤m' = []
  go (suc i') m' m≤m' = artifacts-≉ (ℕ.<⇒≢ (
    begin-strict
      m + 0
    <⟨ ℕ.+-monoʳ-< m (ℕ.n<1+n 0) ⟩
      m + 1
    ≤⟨ ℕ.+-monoˡ-≤ 1 m≤m' ⟩
      m' + 1
    ∎)) ∷ Eq.subst
      (λ x → All (_≉_ (artifact n (m + zero))) (List.concatMap forget-uniqueness x))
      (List.applyUpTo-cong (λ k → Eq.cong (feature n) (Eq.sym (ℕ.+-suc m' (suc k)))) i')
      (go i' (suc m') (ℕ.≤-trans m≤m' (ℕ.n≤1+n m')))
    where
    open ℕ.≤-Reasoning

variant∈fst :
  ∀ (n i : ℕ)
  → i ≤ n
  → variant n i ∈ FST.⟦ fst n ⟧
variant∈fst n i i≤n = fst-config i , Eq.cong ((0 , 0) Rose.-<_>-) (
  begin
    List.applyUpTo (artifact n) (suc i)
  ≡⟨ List.map-applyUpTo id (artifact n) (suc i) ⟨
    List.map (artifact n) (List.upTo (suc i))
  ≡⟨ List.concat-[-] (List.map (artifact n) (List.upTo (suc i))) ⟨
    List.concat (List.map (_∷ []) (List.map (artifact n) (List.upTo (suc i))))
  ≡⟨ Eq.cong List.concat (List.map-∘ {g = (_∷ [])} (List.upTo (suc i))) ⟨
    List.concat (List.map (λ k → artifact n k ∷ []) (List.upTo (suc i)))
  ≡⟨⟩
    List.concat (List.map (λ k → forget-uniqueness (feature n k)) (List.upTo (suc i)))
  ≡⟨ Eq.cong List.concat (List.map-∘ {g = forget-uniqueness} {f = feature n} (List.upTo (suc i))) ⟩
    List.concatMap forget-uniqueness (List.map (feature n) (List.upTo (suc i)))
  ≡⟨ Eq.cong (List.concatMap forget-uniqueness) (List.map-applyUpTo id (feature n) (suc i)) ⟩
    List.concatMap forget-uniqueness (List.applyUpTo (feature n) (suc i))
  ≡⟨ ⊛-all-unique (List.applyUpTo (feature n) (suc i)) (unique-variant n zero (suc i)) ⟨
    forget-uniqueness (⊛-all (List.applyUpTo (feature n) (suc i)))
  ≡⟨ Eq.cong (λ x → forget-uniqueness (⊛-all x)) (select-applyUpTo-feature n n i i≤n) ⟨
    forget-uniqueness (⊛-all (select (fst-config i) (List.applyUpTo (λ m → f m :: feature n m) (suc n))))
  ∎)
  where
  open Eq.≡-Reasoning

⊆⇒All∈ : ∀ {i} n l k
  → k + l ≤ suc n
  → (2cc : 2CC.2CC i NAT)
  → FST.⟦ fst n ⟧ ⊆ 2CC.⟦ 2cc ⟧
  → All (_∈ 2CC.⟦ 2cc ⟧) (List.applyUpTo (λ m → variant n (k + m)) l)
⊆⇒All∈ n zero k l≤n 2cc fst⊆2cc = []
⊆⇒All∈ n (suc l) k l≤n 2cc fst⊆2cc with variant∈fst n k (ℕ.≤-pred (
  begin
    suc k
  ≤⟨ ℕ.m≤m+n (suc k) l ⟩
    suc k + l
  ≡⟨ ℕ.+-suc k l ⟨
    k + suc l
  ≤⟨ l≤n ⟩
    suc n
  ∎))
  where
  open ℕ.≤-Reasoning
⊆⇒All∈ n (suc l) k l≤n 2cc fst⊆2cc | fst-conf , variant≡fst with fst⊆2cc fst-conf
⊆⇒All∈ n (suc l) k l≤n 2cc fst⊆2cc | fst-conf , variant≡fst | 2cc-conf , fst≡2cc =
  (2cc-conf , Eq.subst
    (λ x → variant n x ≡ 2CC.⟦ 2cc ⟧ 2cc-conf)
    (Eq.sym (ℕ.+-identityʳ k))
    (Eq.trans variant≡fst fst≡2cc))
  ∷ Eq.subst
    (All (_∈ 2CC.⟦ 2cc ⟧))
    (List.applyUpTo-cong (λ l → Eq.cong (variant n) (Eq.sym (ℕ.+-suc k l))) l)
    (⊆⇒All∈ n l (suc k) (ℕ.≤-trans (ℕ.≤-reflexive (Eq.sym (ℕ.+-suc k l))) l≤n) 2cc fst⊆2cc)

2*n≤2^n : (n : ℕ) → 2 * n ≤ 2 ^ n
2*n≤2^n zero = ℕ.n≤1+n zero
2*n≤2^n (suc zero) = ℕ.≤-refl
2*n≤2^n (suc n@(suc _)) =
  begin
    2 * suc n
  ≡⟨ ℕ.*-suc 2 n ⟩
    2 + 2 * n
  ≤⟨ ℕ.+-monoˡ-≤ (2 * n) (ℕ.m≤m*n 2 n) ⟩
    2 * n + 2 * n
  ≡⟨ Eq.cong (2 * n +_) (ℕ.+-identityʳ (2 * n)) ⟨
    2 * n + (2 * n + 0)
  ≡⟨⟩
    2 * (2 * n)
  ≤⟨ ℕ.*-monoʳ-≤ 2 (2*n≤2^n n) ⟩
    2 * 2 ^ n
  ≡⟨ ℕ.^-distribˡ-+-* 2 1 n ⟩
    2 ^ suc n
  ∎
  where
  open ℕ.≤-Reasoning

2CC≰FST : Sized2CC F ≰ₛ SizedFST F
2CC≰FST zero = NAT , fst zero , 2CC≽FST (f 0) _==_ (fst zero) , λ 2cc 2cc≅fst → size2CC>0 2cc
2CC≰FST (suc n) = NAT , fst m , 2CC≽FST (f 0) _==_ (fst m) , λ 2cc 2cc≅fst →
  begin-strict
    suc n * sizeFST (fst m)
  <⟨ ℕ.*-monoʳ-< (suc n) (
    begin-strict
      sizeFST (fst m)
    ≡⟨ size-fst m ⟩
      3 + 2 ^ m + 2 * m
    ≤⟨ ℕ.+-monoʳ-≤ (3 + 2 ^ m) (2*n≤2^n m) ⟩
      3 + 2 ^ m + 2 ^ m
    ≤⟨ ℕ.+-monoˡ-≤ (2 ^ m) (ℕ.+-monoˡ-≤ (2 ^ m) (ℕ.m≤m*n 3 (2 ^ m) {{ℕ.>-nonZero (ℕ.m^n>0 2 m)}})) ⟩
      3 * 2 ^ m + 2 ^ m + 2 ^ m
    ≡⟨ Eq.cong (λ x → 3 * 2 ^ m + x + x) (ℕ.*-identityˡ (2 ^ m)) ⟨
      3 * 2 ^ m + 1 * 2 ^ m + 1 * 2 ^ m
    ≡⟨ Eq.cong (_+ 1 * 2 ^ m) (ℕ.*-distribʳ-+ (2 ^ m) 3 1) ⟨
      4 * 2 ^ m + 1 * 2 ^ m
    ≡⟨ ℕ.*-distribʳ-+ (2 ^ m) 4 1 ⟨
      5 * 2 ^ m
    <⟨ ℕ.*-monoˡ-< (2 ^ m) ⦃ ℕ.>-nonZero (ℕ.m^n>0 2 m) ⦄ (ℕ.n<1+n 5) ⟩
      6 * 2 ^ m
    ∎)
  ⟩
    suc n * (6 * 2 ^ m)
  ≡⟨ ℕ.*-assoc (suc n) 6 (2 ^ m) ⟨
    suc n * 6 * 2 ^ m
  ≡⟨ Eq.cong (_* 2 ^ m) (ℕ.*-comm (suc n) 6) ⟩
    6 * suc n * 2 ^ m
  ≡⟨⟩
    m * 2 ^ m
  ≡⟨ Eq.cong (_* 2 ^ m) (List.length-applyUpTo (variant m) m) ⟨
    List.length (List.applyUpTo (variant m) m) * 2 ^ m
  ≤⟨ different-children-counts
       (2 ^ m)
       2cc
       (List.applyUpTo (variant m) m)
       (⊆⇒All∈ m m 0 (ℕ.n≤1+n m) 2cc (proj₂ 2cc≅fst))
       (All.applyUpTo⁺₂ (variant m) m (size-variant m))
       (AllPairs.applyUpTo⁺₁ (variant m) m (λ i<j j<m → variant-≉ m (ℕ.<⇒≢ i<j)))
  ⟩
    size2CC 2cc
  ∎
  where
  open ℕ.≤-Reasoning
  m = 6 * suc n
