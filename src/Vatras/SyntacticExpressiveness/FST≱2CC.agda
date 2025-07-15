module Vatras.SyntacticExpressiveness.FST≱2CC where

open import Data.Bool as Bool using (Bool; true; false; if_then_else_)
import Data.Bool.Properties as Bool
open import Data.Empty using (⊥-elim)
open import Data.Nat as ℕ using (ℕ; suc; zero; _≤_; _<_; z≤n; s≤s; _>_; _+_; _∸_; _*_; _^_)
import Data.Nat.Properties as ℕ
open import Data.Fin as Fin using (Fin; zero; suc)
import Data.Fin.Properties as Fin
open import Data.List as List using (List; []; _∷_)
import Data.List.Properties as List
import Data.List.Membership.Propositional as List
open import Data.List.Relation.Binary.Sublist.Propositional as Sublist using ([]; _∷_; _∷ʳ_)
import Data.List.Relation.Binary.Subset.Propositional as Subset
import Data.List.Relation.Binary.Subset.Propositional.Properties as Subset
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as Unique
open import Data.Product as Prod using (_×_; _,_; proj₁; proj₂; Σ-syntax; ∃-syntax)
import Data.Product.Properties as Prod
open import Data.Unit using (tt)
open import Function using (_∘_; _∘′_; const; id)
open import Function.Bundles using (Equivalence)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Size using (Size; ∞)

open import Vatras.Data.EqIndexedSet using (_⊆_; ⊆-trans; _∈_)
open import Vatras.Framework.Definitions using (𝔸; NAT; atomSize)
open import Vatras.Framework.Variants using (Rose; Rose-injective)
import Vatras.Util.List as List
open import Vatras.Lang.All.Fixed ℕ (Rose ∞)
import Vatras.Lang.2CC.ReflectsVariantSize as 2CC
open import Vatras.SyntacticExpressiveness using (_≱Size_)
open import Vatras.SyntacticExpressiveness.Sizes ℕ using (sizeRose; Sized2CC; size2CC; SizedFST; sizeFST)

NAT' : 𝔸
NAT' = record
  { atoms = ℕ × ℕ
  ; atomsEqual? = Prod.≡-dec ℕ._≟_ ℕ._≟_
  ; atomSize = proj₂
  }

open FST.Impose NAT' hiding (Unique; _∈_)

-- TODO duplicated from 2CC≤CCC
>⇒¬≤ᵇ : ∀ {m n : ℕ} → m > n → Bool.T (Bool.not (m ℕ.≤ᵇ n))
>⇒¬≤ᵇ (s≤s z≤n) = tt
>⇒¬≤ᵇ (s≤s (s≤s m>n)) = >⇒¬≤ᵇ (s≤s m>n)

artifact : ℕ → ℕ → FSTA ∞
artifact n zero = (0 , 2 ^ n) Rose.-< [] >-
artifact n (suc i) = (suc i , 0) Rose.-< [] >-

artifact-wf : (n i : ℕ) → WellFormed (artifact n i)
artifact-wf n zero = [] , []
artifact-wf n (suc i) = [] , []

feature : ℕ → ℕ → FSF
feature n i = (artifact n i ∷ []) ⊚ ([] ∷ [] , artifact-wf n i ∷ [])

fst : ℕ → SPL
fst n = (0 , 0) ◀ List.applyUpTo (λ i → i :: feature n i) (suc n)

size-fst :
  ∀ (n : ℕ)
  → sizeFST (fst n) ≡ 3 + 2 ^ n + 2 * n
size-fst n =
  begin
    sizeFST (fst n)
  ≡⟨⟩
    1 + List.sum (List.map (suc ∘ List.sum ∘ List.map sizeRose ∘ FST.Impose.trees ∘ FST.Impose.impl) (List.applyUpTo (λ i → i :: feature n i) (suc n)))
  ≡⟨⟩
    2 + (sizeRose (artifact n zero) + 0) + List.sum (List.map (suc ∘ List.sum ∘ List.map sizeRose ∘ FST.Impose.trees ∘ FST.Impose.impl) (List.applyUpTo (λ i → suc i :: feature n (suc i)) n))
  ≡⟨ Eq.cong (λ x → 2 + (sizeRose (artifact n zero) + 0 + List.sum (List.map (suc ∘ List.sum ∘ List.map sizeRose ∘ FST.Impose.trees ∘ FST.Impose.impl) x))) (List.map-upTo (λ i → suc i :: feature n (suc i)) n) ⟨
    2 + (sizeRose (artifact n zero) + 0) + List.sum (List.map (suc ∘ List.sum ∘ List.map sizeRose ∘ FST.Impose.trees ∘ FST.Impose.impl) (List.map (λ i → suc i :: feature n (suc i)) (List.upTo n)))
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
variant n i = (0 , 0) Rose.-< List.applyUpTo (artifact n) i >-

size-variant
  : (n i : ℕ)
  → 2 ^ n < sizeRose (variant n (suc i))
size-variant n i =
  begin-strict
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
    sizeRose (variant n (suc i))
  ∎
  where
  open ℕ.≤-Reasoning

1≤size2CC : ∀ {i : Size} {A : 𝔸} → (e : 2CC.2CC i A) → 1 ≤ size2CC e
1≤size2CC (a 2CC.-< cs >-) = s≤s z≤n
1≤size2CC (D 2CC.⟨ l , r ⟩) = s≤s z≤n

-- TODO duplicated in OC≱2CC
variant∈e⇒length-cs
  : ∀ {i} (n l : ℕ) (a : ℕ × ℕ) (cs : List (2CC.2CC i NAT'))
  → variant n (suc l) ∈ 2CC.⟦ a 2CC.-< cs >- ⟧
  → List.length cs ≡ suc l
variant∈e⇒length-cs n l a cs (c , v≡e) =
    List.length cs
  ≡⟨ List.length-map (λ e → 2CC.⟦ e ⟧ c) cs ⟨
    List.length (List.map (λ e → 2CC.⟦ e ⟧ c) cs)
  ≡⟨ Eq.cong List.length (proj₂ (Rose-injective v≡e)) ⟨
    List.length (List.applyUpTo (artifact n) (suc l))
  ≡⟨ List.length-applyUpTo (artifact n) (suc l) ⟩
    suc l
  ∎
  where
  open Eq.≡-Reasoning

-- TODO duplicated in OC≱2CC
partition : ∀ {i : Size} (n D : ℕ)
  → (c₁ c₂ : 2CC.2CC i NAT')
  → (ls : List ℕ)
  → Unique ls
  → All (λ l → variant n (suc l) ∈ 2CC.⟦ D 2CC.⟨ c₁ , c₂ ⟩ ⟧) ls
  → ∃[ ls₁ ] ∃[ ls₂ ]
    ls₁ Subset.⊆ ls × ls₂ Subset.⊆ ls
  × List.length ls₁ + List.length ls₂ ≡ List.length ls
  × Unique ls₁ × All (λ l → variant n (suc l) ∈ 2CC.⟦ c₁ ⟧) ls₁
  × Unique ls₂ × All (λ l → variant n (suc l) ∈ 2CC.⟦ c₂ ⟧) ls₂
partition n D c₁ c₂ [] unique-ls ls⊆2cc =
  [] , [] ,
  Subset.⊆-refl , Subset.⊆-refl ,
  Eq.refl ,
  [] , [] ,
  [] , []
partition n D c₁ c₂ (l ∷ ls) (l∉ls ∷ unique-ls) ((c , l≡2cc) ∷ ls⊆2cc)
  with partition n D c₁ c₂ ls unique-ls ls⊆2cc
... | ls₁ , ls₂ ,
      ls₁⊆ls , ls₂⊆ls ,
      ls₁+ls₂≡ls ,
      unique-ls₁ , ls₁∈l ,
      unique-ls₂ , ls₂∈r
  with c D
... | true =
  l ∷ ls₁ , ls₂ ,
  Subset.∷⁺ʳ l ls₁⊆ls , there ∘ ls₂⊆ls ,
  Eq.cong suc ls₁+ls₂≡ls ,
  All.anti-mono ls₁⊆ls l∉ls ∷ unique-ls₁ , (c , l≡2cc) ∷ ls₁∈l ,
  unique-ls₂ , ls₂∈r
... | false =
  ls₁ , l ∷ ls₂ ,
  there ∘ ls₁⊆ls , Subset.∷⁺ʳ l ls₂⊆ls ,
  Eq.trans
    (ℕ.+-suc (List.length ls₁) (List.length ls₂))
    (Eq.cong suc ls₁+ls₂≡ls) ,
  unique-ls₁ , ls₁∈l ,
  All.anti-mono ls₂⊆ls l∉ls ∷ unique-ls₂ , (c , l≡2cc) ∷ ls₂∈r

-- TODO duplicated in OC≱2CC
big : ∀ {i : Size} (n : ℕ)
  → (2cc : 2CC.2CC i NAT')
  → (ls : List ℕ)
  → Unique ls
  → All (λ l → variant n (suc l) ∈ 2CC.⟦ 2cc ⟧) ls
  → List.length ls * 2 ^ n < size2CC 2cc
big n (a 2CC.-< cs >-) [] unique-ls all-∈ = s≤s z≤n
big n (a 2CC.-< cs >-) (l₁ ∷ []) unique-ls all-∈ =
  begin-strict
    1 * 2 ^ n
  ≡⟨ ℕ.*-identityˡ (2 ^ n) ⟩
    2 ^ n
  <⟨ size-variant n l₁ ⟩
    sizeRose (variant n (suc l₁))
  ≤⟨ 2CC.reflectsVariantSize (variant n (suc l₁)) (a 2CC.-< cs >-) (All.lookup all-∈ (here Eq.refl)) ⟩
    size2CC (a 2CC.-< cs >-)
  ∎
  where
  open ℕ.≤-Reasoning
big n (a 2CC.-< cs >-) (l₁ ∷ l₂ ∷ ls) ((l₁≢l₂ ∷ l₁∉ls) ∷ unique-ls) all-∈ =
  ⊥-elim (l₁≢l₂ (ℕ.suc-injective (Eq.trans
    (Eq.sym (variant∈e⇒length-cs n l₁ a cs (All.lookup all-∈ (here Eq.refl))))
    (variant∈e⇒length-cs n l₂ a cs (All.lookup all-∈ (there (here Eq.refl)))))))
big n (D 2CC.⟨ l , r ⟩) ls unique-ls all-∈ with partition n D l r ls unique-ls all-∈
big n (D 2CC.⟨ l , r ⟩) ls unique-ls all-∈
  | ls₁ , ls₂ ,
    _ , _ ,
    ls₁+ls₂≡ls ,
    unique-ls₁ , ls₁∈l ,
    unique-ls₂ , ls₂∈r =
  begin-strict
    List.length ls * 2 ^ n
  <⟨ ℕ.n<1+n (List.length ls * 2 ^ n) ⟩
    suc (List.length ls * 2 ^ n)
  ≡⟨ Eq.cong (λ x → suc (x * 2 ^ n)) ls₁+ls₂≡ls ⟨
    suc ((List.length ls₁ + List.length ls₂) * 2 ^ n)
  ≡⟨ Eq.cong suc (ℕ.*-distribʳ-+ (2 ^ n) (List.length ls₁) (List.length ls₂)) ⟩
    suc (List.length ls₁ * 2 ^ n + List.length ls₂ * 2 ^ n)
  <⟨ s≤s (ℕ.+-mono-< (big n l ls₁ unique-ls₁ ls₁∈l) (big n r ls₂ unique-ls₂ ls₂∈r)) ⟩
    suc (size2CC l + size2CC r)
  ≡⟨⟩
    size2CC (D 2CC.⟨ l , r ⟩)
  ∎
  where
  open ℕ.≤-Reasoning

fst-config : ℕ → ℕ → Bool
fst-config i f = f ℕ.≤ᵇ i

select-applyUpTo-feature :
  ∀ (k n i : ℕ)
  → i ≤ n
  → select (fst-config i) (List.applyUpTo (λ m → m :: feature k m) (suc n))
  ≡ List.applyUpTo (feature k) (suc i)
select-applyUpTo-feature k n i i≤n =
  begin
    select (fst-config i) (List.applyUpTo (λ m → m :: feature k m) (suc n))
  ≡⟨ Eq.cong (λ x → select (fst-config i) (List.applyUpTo (λ m → m :: feature k m) (suc x))) (ℕ.m+[n∸m]≡n i≤n) ⟨
    select (fst-config i) (List.applyUpTo (λ m → m :: feature k m) (suc (i + (n ∸ i))))
  ≡⟨⟩
    select (fst-config i) (List.applyUpTo (λ m → m :: feature k m) (suc i + offset))
  ≡⟨ selects-init (suc i) zero refl ⟩
    List.applyUpTo (feature k) (suc i)
  ∎
  where
  fst-config≡true : ∀ (j i' : ℕ) → j + suc i' ≡ suc i → fst-config i (j + zero) ≡ true
  fst-config≡true j i' j+i'≡i = Equivalence.to Bool.T-≡ (ℕ.≤⇒≤ᵇ (ℕ.≤-pred (
    begin
      suc j + zero
    ≤⟨ ℕ.+-monoʳ-≤ (suc j) z≤n ⟩
      suc j + i'
    ≡⟨ ℕ.+-suc j i' ⟨
      j + suc i'
    ≡⟨ j+i'≡i ⟩
      suc i
    ∎)))
    where
    open ℕ.≤-Reasoning

  open Eq.≡-Reasoning

  offset : ℕ
  offset = n ∸ i

  deselects-tail : ∀ (i' j : ℕ)
    → select (fst-config i) (List.applyUpTo (λ m → j + m + suc i :: feature k (j + m + suc i)) i')
    ≡ []
  deselects-tail zero j = refl
  deselects-tail (suc i') j =
    begin
      select (fst-config i) (List.applyUpTo (λ m → j + m + suc i :: feature k (j + m + suc i)) (suc i'))
    ≡⟨⟩
      (if fst-config i (j + zero + suc i)
      then feature k (j + zero + suc i) ∷ select (fst-config i) (List.applyUpTo (λ m → j + suc m + suc i :: feature k (j + suc m + suc i)) i')
      else                                select (fst-config i) (List.applyUpTo (λ m → j + suc m + suc i :: feature k (j + suc m + suc i)) i'))
    ≡⟨ Eq.cong (if_then feature k (j + zero + suc i) ∷ select (fst-config i) (List.applyUpTo (λ m → j + suc m + suc i :: feature k (j + suc m + suc i)) i') else select (fst-config i) (List.applyUpTo (λ m → j + suc m + suc i :: feature k (j + suc m + suc i)) i')) (Equivalence.to Bool.T-not-≡ (>⇒¬≤ᵇ (ℕ.m≤n⇒m≤o+n (j + zero) (ℕ.n<1+n i)))) ⟩
      select (fst-config i) (List.applyUpTo (λ m → j + suc m + suc i :: feature k (j + suc m + suc i)) i')
    ≡⟨ Eq.cong (λ x → select (fst-config i) x) (List.applyUpTo-cong (λ m → Eq.cong (λ x → x + suc i :: feature k (x + suc i)) (ℕ.+-suc j m)) i') ⟩
      select (fst-config i) (List.applyUpTo (λ m → suc j + m + suc i :: feature k (suc j + m + suc i)) i')
    ≡⟨ deselects-tail i' (suc j) ⟩
      []
    ∎

  selects-init : ∀ (i' j : ℕ)
    → j + i' ≡ suc i
    → select (fst-config i) (List.applyUpTo (λ m → j + m :: feature k (j + m)) (i' + offset))
    ≡ List.applyUpTo (λ m → feature k (j + m)) i'
  selects-init zero j j+i'≡i =
    begin
      select (fst-config i) (List.applyUpTo (λ m → j + m :: feature k (j + m)) offset)
    ≡⟨ Eq.cong (select (fst-config i)) (List.applyUpTo-cong (λ m → Eq.cong (λ x → x :: feature k x) (ℕ.+-comm j m)) offset) ⟩
      select (fst-config i) (List.applyUpTo (λ m → m + j :: feature k (m + j)) offset)
    ≡⟨ Eq.cong (select (fst-config i)) (List.applyUpTo-cong (λ m → Eq.cong (λ x → m + x :: feature k (m + x)) (Eq.trans (Eq.sym (ℕ.+-identityʳ j)) j+i'≡i)) offset) ⟩
      select (fst-config i) (List.applyUpTo (λ m → m + suc i :: feature k (m + suc i)) offset)
    ≡⟨ deselects-tail offset zero ⟩
      []
    ≡⟨⟩
      List.applyUpTo (λ m → feature k (j + m)) zero
    ∎
  selects-init (suc i') j j+i'≡i =
    begin
      select (fst-config i) (List.applyUpTo (λ m → j + m :: feature k (j + m)) (suc i' + offset))
    ≡⟨⟩
      select (fst-config i) ((j + zero :: feature k (j + zero)) ∷ List.applyUpTo (λ m → j + suc m :: feature k (j + suc m)) (i' + offset))
    ≡⟨⟩
      (if fst-config i (j + zero)
      then feature k (j + zero) ∷ select (fst-config i) (List.applyUpTo (λ m → j + suc m :: feature k (j + suc m)) (i' + offset))
      else                        select (fst-config i) (List.applyUpTo (λ m → j + suc m :: feature k (j + suc m)) (i' + offset)))
    ≡⟨ Eq.cong (if_then feature k (j + zero) ∷ select (fst-config i) (List.applyUpTo (λ m → j + suc m :: feature k (j + suc m)) (i' + offset)) else select (fst-config i) (List.applyUpTo (λ m → j + suc m :: feature k (j + suc m)) (i' + offset))) (fst-config≡true j i' j+i'≡i) ⟩
      feature k (j + zero) ∷ select (fst-config i) (List.applyUpTo (λ m → j + suc m :: feature k (j + suc m)) (i' + offset))
    ≡⟨ Eq.cong (λ x → feature k (j + zero) ∷ select (fst-config i) x) (List.applyUpTo-cong (λ m → Eq.cong₂ _::_ (ℕ.+-suc j m) (Eq.cong (feature k) (ℕ.+-suc j m))) (i' + offset)) ⟩
      feature k (j + zero) ∷ select (fst-config i) (List.applyUpTo (λ m → suc j + m :: feature k (suc j + m)) (i' + offset))
    ≡⟨ Eq.cong (feature k (j + zero) ∷_) (selects-init i' (suc j) (Eq.trans (Eq.sym (ℕ.+-suc j i')) j+i'≡i)) ⟩
      feature k (j + zero) ∷ List.applyUpTo (λ m → feature k (suc j + m)) i'
    ≡⟨ Eq.cong (feature k (j + zero) ∷_) (List.applyUpTo-cong (λ m → Eq.cong (feature k) (Eq.sym (ℕ.+-suc j m))) i') ⟩
      feature k (j + zero) ∷ List.applyUpTo (λ m → feature k (j + suc m)) i'
    ≡⟨⟩
      List.applyUpTo (λ m → feature k (j + m)) (suc i')
    ∎

forget-uniqueness-⊛-all :
  ∀ (as : List FSF)
  → forget-uniqueness (⊛-all as) ≡ List.foldr _⊕_ [] (List.map forget-uniqueness as)
forget-uniqueness-⊛-all [] = refl
forget-uniqueness-⊛-all (a ∷ as) =
  begin
    forget-uniqueness (⊛-all (a ∷ as))
  ≡⟨⟩
    forget-uniqueness (a ⊛ (⊛-all as))
  ≡⟨⟩
    forget-uniqueness a ⊕ forget-uniqueness (⊛-all as)
  ≡⟨ Eq.cong (λ x → forget-uniqueness a ⊕ x) (forget-uniqueness-⊛-all as) ⟩
    forget-uniqueness a ⊕ List.foldr _⊕_ [] (List.map forget-uniqueness as)
  ≡⟨⟩
    List.foldr _⊕_ [] (forget-uniqueness a ∷ List.map forget-uniqueness as)
  ≡⟨⟩
    List.foldr _⊕_ [] (List.map forget-uniqueness (a ∷ as))
  ∎
  where
  open Eq.≡-Reasoning

artifacts⊙artifact :
  ∀ (n i k : ℕ)
  → List.applyUpTo (λ m → artifact n (m + k)) i ⊙ artifact n (i + k)
  ≡ List.applyUpTo (λ m → artifact n (m + k)) (suc i)
artifacts⊙artifact n zero k = refl
artifacts⊙artifact n (suc i) k with artifact n (suc i + k) == artifact n k
artifacts⊙artifact n (suc i) k | no _ =
  begin
    artifact n k ∷ (List.applyUpTo (λ m → artifact n (suc m + k)) i ⊙ artifact n (suc i + k))
  ≡⟨ Eq.cong (λ x → artifact n k ∷ (x ⊙ artifact n (suc i + k))) (List.applyUpTo-cong (λ m → Eq.cong (artifact n) (ℕ.+-suc m k)) i) ⟨
    artifact n k ∷ (List.applyUpTo (λ m → artifact n (m + suc k)) i ⊙ artifact n (suc i + k))
  ≡⟨ Eq.cong (λ x → artifact n k ∷ (List.applyUpTo (λ m → artifact n (m + suc k)) i ⊙ artifact n x)) (ℕ.+-suc i k) ⟨
    artifact n k ∷ (List.applyUpTo (λ m → artifact n (m + suc k)) i ⊙ artifact n (i + suc k))
  ≡⟨ Eq.cong (artifact n k ∷_) (artifacts⊙artifact n i (suc k)) ⟩
    artifact n k ∷ List.applyUpTo (λ m → artifact n (m + suc k)) (suc i)
  ≡⟨ Eq.cong (artifact n k ∷_) (List.applyUpTo-cong (λ m → Eq.cong (artifact n) (ℕ.+-suc m k)) (suc i)) ⟩
    artifact n k ∷ List.applyUpTo (λ m → artifact n (suc m + k)) (suc i)
  ≡⟨⟩
    List.applyUpTo (λ m → artifact n (m + k)) (suc (suc i))
  ∎
  where
  open Eq.≡-Reasoning
artifacts⊙artifact n (suc i) (suc k) | yes artifact-1+i+k≈artifact-k = ⊥-elim (ℕ.1+n≰n (ℕ.≤-trans (ℕ.m≤n+m (suc k) i) (ℕ.≤-reflexive (ℕ.suc-injective (Prod.,-injectiveˡ artifact-1+i+k≈artifact-k)))))

artifact⊕artifacts :
  ∀ (n i k : ℕ)
  → (artifact n k ∷ []) ⊕ List.applyUpTo (λ m → artifact n (suc m + k)) i
  ≡ List.applyUpTo (λ m → artifact n (m + k)) (suc i)
artifact⊕artifacts n i k = go 1 i k
  where
  go : ∀ (i j k : ℕ)
    → List.applyUpTo (λ m → artifact n (m + k)) i ⊕ List.applyUpTo (λ m → artifact n (i + m + k)) j
    ≡ List.applyUpTo (λ m → artifact n (m + k)) (i + j)
  go i zero k = Eq.cong (List.applyUpTo (λ m → artifact n (m + k))) (Eq.sym (ℕ.+-identityʳ i))
  go i (suc j) k =
    begin
      List.applyUpTo (λ m → artifact n (m + k)) i ⊕ List.applyUpTo (λ m → artifact n (i + m + k)) (suc j)
    ≡⟨⟩
      List.applyUpTo (λ m → artifact n (m + k)) i ⊕ (artifact n (i + zero + k) ∷ List.applyUpTo (λ m → artifact n (i + suc m + k)) j)
    ≡⟨ Eq.cong (λ x → List.applyUpTo (λ m → artifact n (m + k)) i ⊕ (artifact n (x + k) ∷ List.applyUpTo (λ m → artifact n (i + suc m + k)) j)) (ℕ.+-identityʳ i) ⟩
      List.applyUpTo (λ m → artifact n (m + k)) i ⊕ (artifact n (i + k) ∷ List.applyUpTo (λ m → artifact n (i + suc m + k)) j)
    ≡⟨⟩
      (List.applyUpTo (λ m → artifact n (m + k)) i ⊙ artifact n (i + k)) ⊕ List.applyUpTo (λ m → artifact n (i + suc m + k)) j
    ≡⟨ Eq.cong (_⊕ List.applyUpTo (λ m → artifact n (i + suc m + k)) j) (artifacts⊙artifact n i k) ⟩
      List.applyUpTo (λ m → artifact n (m + k)) (suc i) ⊕ List.applyUpTo (λ m → artifact n (i + suc m + k)) j
    ≡⟨ Eq.cong (λ x → List.applyUpTo (λ m → artifact n (m + k)) (suc i) ⊕ x) (List.applyUpTo-cong (λ m → Eq.cong (λ x → artifact n (x + k)) (ℕ.+-suc i m)) j) ⟩
      List.applyUpTo (λ m → artifact n (m + k)) (suc i) ⊕ List.applyUpTo (λ m → artifact n (suc i + m + k)) j
    ≡⟨ go (suc i) j k ⟩
      List.applyUpTo (λ m → artifact n (m + k)) (suc i + j)
    ≡⟨ Eq.cong (List.applyUpTo (λ m → artifact n (m + k))) (ℕ.+-suc i j) ⟨
      List.applyUpTo (λ m → artifact n (m + k)) (i + suc j)
    ∎
    where
    open Eq.≡-Reasoning

foldr-⊕-artifacts :
  ∀ (n i : ℕ)
  → List.applyUpTo (artifact n) i
  ≡ List.foldr _⊕_ [] (List.applyUpTo (λ m → artifact n m ∷ []) i)
foldr-⊕-artifacts n i = go i zero
  where
  open Eq.≡-Reasoning

  go :
    ∀ (i j : ℕ)
    → List.applyUpTo (λ m → artifact n (j + m)) i
    ≡ List.foldr _⊕_ [] (List.applyUpTo (λ m → artifact n (j + m) ∷ []) i)
  go zero j = refl
  go (suc i) j =
    begin
      List.applyUpTo (λ m → artifact n (j + m)) (suc i)
    ≡⟨ List.applyUpTo-cong (λ m → Eq.cong (artifact n) (ℕ.+-comm j m)) (suc i) ⟩
      List.applyUpTo (λ m → artifact n (m + j)) (suc i)
    ≡⟨ artifact⊕artifacts n i j ⟨
      (artifact n j ∷ []) ⊕ List.applyUpTo (λ m → artifact n (suc m + j)) i
    ≡⟨ Eq.cong ((artifact n j ∷ []) ⊕_) (List.applyUpTo-cong (λ m → Eq.cong (λ x → artifact n (suc x)) (ℕ.+-comm m j)) i) ⟩
      (artifact n j ∷ []) ⊕ List.applyUpTo (λ m → artifact n (suc j + m)) i
    ≡⟨ Eq.cong ((artifact n j ∷ []) ⊕_) (go i (suc j)) ⟩
      (artifact n j ∷ []) ⊕ List.foldr _⊕_ [] (List.applyUpTo (λ m → artifact n (suc j + m) ∷ []) i)
    ≡⟨ Eq.cong (λ x → (artifact n j ∷ []) ⊕ List.foldr _⊕_ [] x) (List.applyUpTo-cong (λ m → Eq.cong (λ x → artifact n x ∷ []) (ℕ.+-suc j m)) i) ⟨
      (artifact n j ∷ []) ⊕ List.foldr _⊕_ [] (List.applyUpTo (λ m → artifact n (j + suc m) ∷ []) i)
    ≡⟨⟩
      List.foldr _⊕_ [] ((artifact n j ∷ []) ∷ List.applyUpTo (λ m → artifact n (j + suc m) ∷ []) i)
    ≡⟨ Eq.cong (λ x → List.foldr _⊕_ [] ((artifact n x ∷ []) ∷ List.applyUpTo (λ m → artifact n (j + suc m) ∷ []) i)) (ℕ.+-identityʳ j) ⟨
      List.foldr _⊕_ [] ((artifact n (j + zero) ∷ []) ∷ List.applyUpTo (λ m → artifact n (j + suc m) ∷ []) i)
    ≡⟨⟩
      List.foldr _⊕_ [] (List.applyUpTo (λ m → artifact n (j + m) ∷ []) (suc i))
    ∎

variant∈fst :
  ∀ (n i : ℕ)
  → i ≤ n
  → variant n (suc i) ∈ FST.⟦ fst n ⟧
variant∈fst n i i≤n = fst-config i , Eq.cong ((0 , 0) Rose.-<_>-) (
  begin
    List.applyUpTo (artifact n) (suc i)
  ≡⟨ foldr-⊕-artifacts n (suc i) ⟩
    List.foldr _⊕_ [] (List.applyUpTo (λ m → artifact n m ∷ []) (suc i))
  ≡⟨⟩
    List.foldr _⊕_ [] (List.applyUpTo (forget-uniqueness ∘ feature n) (suc i))
  ≡⟨ Eq.cong (λ x → List.foldr _⊕_ [] x) (List.map-applyUpTo forget-uniqueness (feature n) (suc i)) ⟨
    List.foldr _⊕_ [] (List.map forget-uniqueness (List.applyUpTo (feature n) (suc i)))
  ≡⟨ forget-uniqueness-⊛-all (List.applyUpTo (feature n) (suc i)) ⟨
    forget-uniqueness (⊛-all (List.applyUpTo (feature n) (suc i)))
  ≡⟨ Eq.cong (λ x → forget-uniqueness (⊛-all x)) (select-applyUpTo-feature n n i i≤n) ⟨
    forget-uniqueness (⊛-all (select (fst-config i) (List.applyUpTo (λ m → m :: feature n m) (suc n))))
  ∎)
  where
  open Eq.≡-Reasoning

⊆⇒All∈ : ∀ {i} n l k
  → k + l ≤ suc n
  → (2cc : 2CC.2CC i NAT')
  → FST.⟦ fst n ⟧ ⊆ 2CC.⟦ 2cc ⟧
  → All (λ l → variant n (suc l) ∈ 2CC.⟦ 2cc ⟧) (List.applyUpTo (k +_) l)
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
    (λ x → variant n (suc x) ≡ 2CC.⟦ 2cc ⟧ 2cc-conf)
    (Eq.sym (ℕ.+-identityʳ k))
    (Eq.trans variant≡fst fst≡2cc))
  ∷ Eq.subst
    (All (λ l → variant n (suc l) ∈ 2CC.⟦ 2cc ⟧))
    (List.applyUpTo-cong (λ l → Eq.sym (ℕ.+-suc k l)) l)
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

FST≱2CC : SizedFST ≱Size Sized2CC
FST≱2CC zero = NAT' , fst zero , λ 2cc fst≅2cc → 1≤size2CC 2cc
FST≱2CC (suc n) = NAT' , fst m , λ 2cc fst≅2cc →
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
  ≡⟨ Eq.cong (_* 2 ^ m) (List.length-upTo m) ⟨
    List.length (List.upTo m) * 2 ^ m
  <⟨ big m 2cc (List.upTo m) (Unique.applyUpTo⁺₁ id m (λ i<j j<n → ℕ.<⇒≢ i<j)) (⊆⇒All∈ m m 0 (ℕ.n≤1+n m) 2cc (proj₁ fst≅2cc)) ⟩
    size2CC 2cc
  ∎
  where
  open ℕ.≤-Reasoning
  m = 6 * suc n
