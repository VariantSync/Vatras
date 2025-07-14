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
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as Unique
open import Data.Product as Prod using (_×_; _,_; proj₁; proj₂; Σ-syntax)
import Data.Product.Properties as Prod
open import Data.Unit using (tt)
open import Function using (_∘_; _∘′_; const)
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

big-artifact : ℕ → ℕ → FSTA ∞
big-artifact n i = (i , 2 ^ n) Rose.-< [] >-

artifact : ℕ → ℕ → FSTA ∞
artifact n zero = (0 , 0) Rose.-< big-artifact n zero ∷ [] >-
artifact n (suc i) = (suc i , 0) Rose.-< [] >-

big-artifact-wf : (n i : ℕ) → WellFormed (big-artifact n i)
big-artifact-wf n i = [] , []

artifact-wf : (n i : ℕ) → WellFormed (artifact n i)
artifact-wf n zero = [] ∷ [] , big-artifact-wf n zero ∷ []
artifact-wf n (suc i) = [] , []

feature : ℕ → ℕ → FSF
feature n i = (artifact n i ∷ []) ⊚ ([] ∷ [] , artifact-wf n i ∷ [])

fst : ℕ → SPL
fst n = (0 , 0) ◀ List.applyUpTo (λ i → i :: feature n i) (suc n)

size-big-artifact :
  ∀ (n i : ℕ)
  → sizeRose (big-artifact n i) ≡ suc (2 ^ n)
size-big-artifact n i =
  begin
    sizeRose (big-artifact n i)
  ≡⟨⟩
    suc (2 ^ n) + 0
  ≡⟨ ℕ.+-identityʳ (suc (2 ^ n)) ⟩
    suc (2 ^ n)
  ∎
  where
  open Eq.≡-Reasoning

size-fst :
  ∀ (n : ℕ)
  → sizeFST (fst n) ≡ 4 + 2 ^ n + 2 * n
size-fst n =
  begin
    sizeFST (fst n)
  ≡⟨⟩
    suc (List.sum (List.map (suc ∘ List.sum ∘ List.map sizeRose ∘ FST.Impose.trees ∘ FST.Impose.impl) (List.applyUpTo (λ i → i :: feature n i) (suc n))))
  ≡⟨⟩
    suc (suc (sizeRose (artifact n zero) + 0) + List.sum (List.map (suc ∘ List.sum ∘ List.map sizeRose ∘ FST.Impose.trees ∘ FST.Impose.impl) (List.applyUpTo (λ i → suc i :: feature n (suc i)) n)))
  ≡⟨ Eq.cong (λ x → suc (suc (sizeRose (artifact n zero) + 0) + List.sum (List.map (suc ∘ List.sum ∘ List.map sizeRose ∘ FST.Impose.trees ∘ FST.Impose.impl) x))) (List.map-upTo (λ i → suc i :: feature n (suc i)) n) ⟨
    suc (suc (sizeRose (artifact n zero) + 0) + List.sum (List.map (suc ∘ List.sum ∘ List.map sizeRose ∘ FST.Impose.trees ∘ FST.Impose.impl) (List.map (λ i → suc i :: feature n (suc i)) (List.upTo n))))
  ≡⟨ Eq.cong (λ x → suc (suc (sizeRose (artifact n zero) + 0) + List.sum x)) (List.map-∘ (List.upTo n)) ⟨
    3 + sizeRose (big-artifact n zero) + 0 + 0 + List.sum (List.map (λ i → suc (sizeRose (artifact n (suc i)) + 0)) (List.upTo n))
  ≡⟨ Eq.cong₂ (λ x y → x + 0 + List.sum y) (ℕ.+-identityʳ (3 + sizeRose (big-artifact n zero))) (List.map-cong (λ i → Eq.cong suc (ℕ.+-identityʳ (sizeRose (artifact n (suc i))))) (List.upTo n)) ⟩
    3 + sizeRose (big-artifact n zero) + 0 + List.sum (List.map (λ i → suc (sizeRose (artifact n (suc i)))) (List.upTo n))
  ≡⟨ Eq.cong (λ x → x + List.sum (List.map (λ i → suc (sizeRose (artifact n (suc i)))) (List.upTo n))) (ℕ.+-identityʳ (3 + sizeRose (big-artifact n zero))) ⟩
    3 + sizeRose (big-artifact n zero) + List.sum (List.map (const 2) (List.upTo n))
  ≡⟨ Eq.cong (λ x → 3 + x + List.sum (List.map (const 2) (List.upTo n))) (size-big-artifact n zero) ⟩
    4 + 2 ^ n + List.sum (List.map (const 2) (List.upTo n))
  ≡⟨ Eq.cong (λ x → 4 + 2 ^ n + List.sum x) (List.map-const 2 (List.upTo n)) ⟩
    4 + 2 ^ n + List.sum (List.replicate (List.length (List.upTo n)) 2)
  ≡⟨ Eq.cong (λ x → 4 + 2 ^ n + List.sum (List.replicate x 2)) (List.length-upTo n) ⟩
    4 + 2 ^ n + List.sum (List.replicate n 2)
  ≡⟨ Eq.cong (λ x → 4 + 2 ^ n + x) (List.sum-replicate n 2) ⟩
    4 + 2 ^ n + n * 2
  ≡⟨ Eq.cong (4 + 2 ^ n +_) (ℕ.*-comm n 2) ⟩
    4 + 2 ^ n + 2 * n
  ∎
  where
  open Eq.≡-Reasoning

variant : ℕ → ℕ → FSTA ∞
variant n i = (0 , 0) Rose.-< List.applyUpTo (artifact n) i >-

1≤size2CC : ∀ {i : Size} {A : 𝔸} → (e : 2CC.2CC i A) → 1 ≤ size2CC e
1≤size2CC (a 2CC.2CC.-< cs >-) = s≤s z≤n
1≤size2CC (D 2CC.2CC.⟨ l , r ⟩) = s≤s z≤n

∈-children : ∀ {i : Size}
  → (n j : ℕ)
  → {a₁ a₂ : ℕ × ℕ}
  → (cs₁ : List (FSTA ∞))
  → (cs₂ : List (2CC.2CC i NAT'))
  → (a₁ Rose.-< cs₁ >-) ∈ 2CC.⟦ a₂ 2CC.2CC.-< cs₂ >- ⟧
  → cs₁ ∈ (λ conf → List.map (λ c → 2CC.⟦ c ⟧ conf) cs₂)
∈-children n j cs₁ cs₂ (conf , cs₁≡cs₂) = conf , proj₂ (Rose-injective cs₁≡cs₂)

big-artifact∈2cc⇒2^n≤2cc : ∀ {i : Size}
  → (n j : ℕ)
  → (2cc : 2CC.2CC i NAT')
  → big-artifact n j ∈ 2CC.⟦ 2cc ⟧
  → 2 ^ n < size2CC 2cc
big-artifact∈2cc⇒2^n≤2cc n j (a 2CC.2CC.-< cs >-) (conf , artifact≡2cc) with proj₁ (Rose-injective artifact≡2cc)
big-artifact∈2cc⇒2^n≤2cc n j (.(j , 2 ^ n) 2CC.-< cs >-) (conf , artifact≡2cc) | refl =
  begin-strict
    2 ^ n
  <⟨ ℕ.n<1+n (2 ^ n) ⟩
    suc (2 ^ n)
  ≤⟨ s≤s (ℕ.m≤m+n (2 ^ n) (List.sum (List.map size2CC cs))) ⟩
    suc (2 ^ n + List.sum (List.map size2CC cs))
  ≡⟨⟩
    size2CC ((j , 2 ^ n) 2CC.2CC.-< cs >-)
  ∎
  where
  open ℕ.≤-Reasoning
big-artifact∈2cc⇒2^n≤2cc n j (D 2CC.2CC.⟨ l , r ⟩) (conf , artifact≡2cc) with conf D
big-artifact∈2cc⇒2^n≤2cc n j (D 2CC.2CC.⟨ l , r ⟩) (conf , artifact≡2cc) | true =
  begin-strict
    2 ^ n
  <⟨ s≤s ℕ.≤-refl ⟩
    suc (2 ^ n)
  <⟨ s≤s (big-artifact∈2cc⇒2^n≤2cc n j l (conf , artifact≡2cc)) ⟩
    suc (size2CC l)
  ≤⟨ s≤s (ℕ.m≤m+n (size2CC l) (size2CC r)) ⟩
    suc (size2CC l + size2CC r)
  ≡⟨⟩
    size2CC (D 2CC.2CC.⟨ l , r ⟩)
  ∎
  where
  open ℕ.≤-Reasoning
big-artifact∈2cc⇒2^n≤2cc n j (D 2CC.2CC.⟨ l , r ⟩) (conf , artifact≡2cc) | false =
  begin-strict
    2 ^ n
  <⟨ ℕ.n<1+n (2 ^ n) ⟩
    suc (2 ^ n)
  <⟨ s≤s (big-artifact∈2cc⇒2^n≤2cc n j r (conf , artifact≡2cc)) ⟩
    suc (size2CC r)
  ≤⟨ s≤s (ℕ.m≤n+m (size2CC r) (size2CC l)) ⟩
    suc (size2CC l + size2CC r)
  ≡⟨⟩
    size2CC (D 2CC.2CC.⟨ l , r ⟩)
  ∎
  where
  open ℕ.≤-Reasoning

artifact-0∈2cc⇒2^n≤2cc : ∀ {i : Size}
  → (n : ℕ)
  → (2cc : 2CC.2CC i NAT')
  → artifact n zero ∈ 2CC.⟦ 2cc ⟧
  → 2 ^ n ≤ size2CC 2cc
artifact-0∈2cc⇒2^n≤2cc n (a 2CC.2CC.-< c ∷ [] >-) (conf , artifact≡cs) =
  begin
    2 ^ n
  <⟨ ℕ.n<1+n (2 ^ n) ⟩
    suc (2 ^ n)
  <⟨ s≤s (big-artifact∈2cc⇒2^n≤2cc n zero c (conf , List.∷-injectiveˡ (proj₂ (Rose-injective artifact≡cs)))) ⟩
    suc (size2CC c)
  ≡⟨ Eq.cong suc (ℕ.+-identityʳ (size2CC c)) ⟨
    suc (size2CC c + 0)
  ≤⟨ s≤s (ℕ.m≤n+m (size2CC c + 0) (atomSize NAT' a)) ⟩
    suc (atomSize NAT' a + (size2CC c + 0))
  ≡⟨⟩
    size2CC (a 2CC.2CC.-< c ∷ [] >-)
  ∎
  where
  open ℕ.≤-Reasoning
artifact-0∈2cc⇒2^n≤2cc n (D 2CC.2CC.⟨ l , r ⟩) (conf , artifact≡cs) with conf D
artifact-0∈2cc⇒2^n≤2cc n (D 2CC.2CC.⟨ l , r ⟩) (conf , artifact≡cs) | true =
  begin
    2 ^ n
  <⟨ ℕ.n<1+n (2 ^ n) ⟩
    suc (2 ^ n)
  ≤⟨ s≤s (artifact-0∈2cc⇒2^n≤2cc n l (conf , artifact≡cs)) ⟩
    suc (size2CC l)
  ≤⟨ s≤s (ℕ.m≤m+n (size2CC l) (size2CC r)) ⟩
    suc (size2CC l + size2CC r)
  ≡⟨⟩
    size2CC (D 2CC.2CC.⟨ l , r ⟩)
  ∎
  where
  open ℕ.≤-Reasoning
artifact-0∈2cc⇒2^n≤2cc n (D 2CC.2CC.⟨ l , r ⟩) (conf , artifact≡cs) | false =
  begin
    2 ^ n
  <⟨ ℕ.n<1+n (2 ^ n) ⟩
    suc (2 ^ n)
  ≤⟨ s≤s (artifact-0∈2cc⇒2^n≤2cc n r (conf , artifact≡cs)) ⟩
    suc (size2CC r)
  ≤⟨ s≤s (ℕ.m≤n+m (size2CC r) (size2CC l)) ⟩
    suc (size2CC l + size2CC r)
  ≡⟨⟩
    size2CC (D 2CC.2CC.⟨ l , r ⟩)
  ∎
  where
  open ℕ.≤-Reasoning

2^n≤size2CC-artifact : ∀ {i : Size}
  → (n j : ℕ)
  → (a : ℕ × ℕ)
  → (cs : List (2CC.2CC i NAT'))
  → variant n (suc j) ∈ 2CC.⟦ a 2CC.-< cs >- ⟧
  → 2 ^ n ≤ size2CC (a 2CC.-< cs >-)
2^n≤size2CC-artifact n j a (c ∷ cs) (conf , artifact≡cs) =
  begin
    2 ^ n
  ≤⟨ artifact-0∈2cc⇒2^n≤2cc n c (conf , List.∷-injectiveˡ (proj₂ (Rose-injective artifact≡cs))) ⟩
    size2CC c
  ≤⟨ ℕ.m≤m+n (size2CC c) (List.sum (List.map size2CC cs)) ⟩
    size2CC c + List.sum (List.map size2CC cs)
  ≡⟨⟩
    List.sum (List.map size2CC (c ∷ cs))
  <⟨ s≤s ℕ.≤-refl ⟩
    suc (List.sum (List.map size2CC (c ∷ cs)))
  ≤⟨ s≤s (ℕ.m≤n+m (List.sum (List.map size2CC (c ∷ cs))) (atomSize NAT' a)) ⟩
    suc (atomSize NAT' a + List.sum (List.map size2CC (c ∷ cs)))
  ≡⟨⟩
    size2CC (a 2CC.-< c ∷ cs >-)
  ∎
  where
  open ℕ.≤-Reasoning

impossible-artifact-sizes : ∀ {i : Size}
  → (n : ℕ)
  → (cs : List (2CC.2CC i NAT'))
  → (cs₁ cs₂ : List (FSTA ∞))
  → List.length cs₁ ≢ List.length cs₂
  → cs₁ ∈ (λ conf → List.map (λ c → 2CC.⟦ c ⟧ conf) cs)
  → ¬ cs₂ ∈ (λ conf → List.map (λ c → 2CC.⟦ c ⟧ conf) cs)
impossible-artifact-sizes n cs       []         []         cs₁≢cs₂ (i , cs₁≡cs) (j , cs₂≡cs) = cs₁≢cs₂ refl
impossible-artifact-sizes n []       []         (c₂ ∷ cs₂) cs₁≢cs₂ (i , cs₁≡cs) (j , ())
impossible-artifact-sizes n (c ∷ cs) []         (c₂ ∷ cs₂) cs₁≢cs₂ (i , ())     (j , cs₂≡cs)
impossible-artifact-sizes n []       (c₁ ∷ cs₁) []         cs₁≢cs₂ (i , ())     (j , cs₂≡cs)
impossible-artifact-sizes n (c ∷ cs) (c₁ ∷ cs₁) []         cs₁≢cs₂ (i , cs₁≡cs) (j , ())
impossible-artifact-sizes n (c ∷ cs) (c₁ ∷ cs₁) (c₂ ∷ cs₂) cs₁≢cs₂ (i , cs₁≡cs) (j , cs₂≡cs) =
  impossible-artifact-sizes n cs cs₁ cs₂ (cs₁≢cs₂ ∘ Eq.cong suc) (i , List.∷-injectiveʳ cs₁≡cs) (j , List.∷-injectiveʳ cs₂≡cs)

split-sizes : ∀ {i : Size}
  → (n : ℕ)
  → (D : ℕ)
  → (l r : 2CC.2CC i NAT')
  → (sizes : List ℕ)
  → (variant n ∘ suc ∘ List.lookup sizes) ⊆ 2CC.⟦ D 2CC.2CC.⟨ l , r ⟩ ⟧
  → List ℕ × List ℕ
split-sizes n D l r [] artifact∈l,r = [] , []
split-sizes n D l r (size ∷ sizes) artifact⊆l,r with artifact⊆l,r zero
split-sizes n D l r (size ∷ sizes) artifact⊆l,r | conf , artifact≡l,r with conf D
split-sizes n D l r (size ∷ sizes) artifact⊆l,r | conf , artifact≡l,r | true = Prod.map₁ (size ∷_) (split-sizes n D l r sizes (artifact⊆l,r ∘ suc))
split-sizes n D l r (size ∷ sizes) artifact⊆l,r | conf , artifact≡l,r | false = Prod.map₂ (size ∷_) (split-sizes n D l r sizes (artifact⊆l,r ∘ suc))

split-sizes⊆ : ∀ {i : Size}
  → (n : ℕ)
  → (D : ℕ)
  → (l r : 2CC.2CC i NAT')
  → (sizes : List ℕ)
  → (artifact∈l,r : (variant n ∘ suc ∘ List.lookup sizes) ⊆ 2CC.⟦ D 2CC.2CC.⟨ l , r ⟩ ⟧)
  → ((variant n ∘′ suc ∘′ List.lookup (proj₁ (split-sizes n D l r sizes artifact∈l,r))) ⊆ 2CC.⟦ l ⟧)
  × ((variant n ∘′ suc ∘′ List.lookup (proj₂ (split-sizes n D l r sizes artifact∈l,r))) ⊆ 2CC.⟦ r ⟧)
split-sizes⊆ n D l r [] artifact∈l,r = (λ where ()) , (λ where ())
split-sizes⊆ n D l r (size ∷ sizes) artifact⊆l,r with artifact⊆l,r zero
split-sizes⊆ n D l r (size ∷ sizes) artifact⊆l,r | conf , artifact≡l,r with conf D
split-sizes⊆ n D l r (size ∷ sizes) artifact⊆l,r | conf , artifact≡l,r | true = Prod.map₁ go (split-sizes⊆ n D l r sizes (artifact⊆l,r ∘ suc))
  where
  go : ∀ {sizes : List ℕ}
    → ((variant n ∘′ suc ∘′ List.lookup sizes) ⊆ 2CC.⟦ l ⟧)
    → (variant n ∘′ suc ∘′ List.lookup (size ∷ sizes)) ⊆ 2CC.⟦ l ⟧
  go artifact⊆l zero = conf , artifact≡l,r
  go artifact⊆l (suc i) = artifact⊆l i
split-sizes⊆ n D l r (size ∷ sizes) artifact⊆l,r | conf , artifact≡l,r | false = Prod.map₂ go (split-sizes⊆ n D l r sizes (artifact⊆l,r ∘ suc))
  where
  go : ∀ {sizes : List ℕ}
    → ((variant n ∘′ suc ∘′ List.lookup sizes) ⊆ 2CC.⟦ r ⟧)
    → (variant n ∘′ suc ∘′ List.lookup (size ∷ sizes)) ⊆ 2CC.⟦ r ⟧
  go artifact⊆r zero = conf , artifact≡l,r
  go artifact⊆r (suc i) = artifact⊆r i

split-sizes-length : ∀ {i : Size}
  → (n : ℕ)
  → (D : ℕ)
  → (l r : 2CC.2CC i NAT')
  → (sizes : List ℕ)
  → (artifact∈l,r : (variant n ∘ suc ∘ List.lookup sizes) ⊆ 2CC.⟦ D 2CC.2CC.⟨ l , r ⟩ ⟧)
  → List.length sizes ≤ List.length (proj₁ (split-sizes n D l r sizes artifact∈l,r)) + List.length (proj₂ (split-sizes n D l r sizes artifact∈l,r))
split-sizes-length n D l r [] artifact∈l,r = z≤n
split-sizes-length n D l r (size ∷ sizes) artifact⊆l,r with artifact⊆l,r zero
split-sizes-length n D l r (size ∷ sizes) artifact⊆l,r | conf , artifact≡l,r with conf D
split-sizes-length n D l r (size ∷ sizes) artifact∈l,r | conf , artifact≡l,r | true = s≤s (split-sizes-length n D l r sizes (artifact∈l,r ∘ suc))
split-sizes-length n D l r (size ∷ sizes) artifact∈l,r | conf , artifact≡l,r | false =
  begin
    List.length (size ∷ sizes)
  ≡⟨⟩
    suc (List.length sizes)
  ≤⟨ s≤s (split-sizes-length n D l r sizes (artifact∈l,r ∘ suc)) ⟩
    suc (List.length (proj₁ (split-sizes n D l r sizes (artifact∈l,r ∘ suc))) + List.length (proj₂ (split-sizes n D l r sizes (artifact∈l,r ∘ suc))))
  ≡⟨ ℕ.+-suc (List.length (proj₁ (split-sizes n D l r sizes (artifact∈l,r ∘ suc)))) (List.length (proj₂ (split-sizes n D l r sizes (artifact∈l,r ∘ suc)))) ⟨
    List.length (proj₁ (split-sizes n D l r sizes (artifact∈l,r ∘ suc))) + suc (List.length (proj₂ (split-sizes n D l r sizes (artifact∈l,r ∘ suc))))
  ∎
  where
  open ℕ.≤-Reasoning

split-sizes-sublist : ∀ {i : Size}
  → (n : ℕ)
  → (D : ℕ)
  → (l r : 2CC.2CC i NAT')
  → (sizes : List ℕ)
  → (artifact∈l,r : (variant n ∘ suc ∘ List.lookup sizes) ⊆ 2CC.⟦ D 2CC.2CC.⟨ l , r ⟩ ⟧)
  → proj₁ (split-sizes n D l r sizes artifact∈l,r) Sublist.⊆ sizes
  × proj₂ (split-sizes n D l r sizes artifact∈l,r) Sublist.⊆ sizes
split-sizes-sublist n D l r [] artifact∈l,r = [] , []
split-sizes-sublist n D l r (size ∷ sizes) artifact⊆l,r with artifact⊆l,r zero
split-sizes-sublist n D l r (size ∷ sizes) artifact⊆l,r | conf , artifact≡l,r with conf D
split-sizes-sublist n D l r (size ∷ sizes) artifact∈l,r | conf , artifact≡l,r | true = Prod.map (refl ∷_) (size ∷ʳ_) (split-sizes-sublist n D l r sizes (artifact∈l,r ∘ suc))
split-sizes-sublist n D l r (size ∷ sizes) artifact∈l,r | conf , artifact≡l,r | false = Prod.map (size ∷ʳ_) (refl ∷_) (split-sizes-sublist n D l r sizes (artifact∈l,r ∘ suc))

n*2^n≤size2CC : ∀ {i : Size}
  → (n : ℕ)
  → (2cc : 2CC.2CC i NAT')
  → (sizes : List ℕ)
  → Unique sizes
  → (variant n ∘ suc ∘ List.lookup sizes) ⊆ 2CC.⟦ 2cc ⟧
  → List.length sizes * 2 ^ n ≤ size2CC 2cc
n*2^n≤size2CC n (a 2CC.2CC.-< cs >-) [] unique-sizes sizes⊆2cc = z≤n
n*2^n≤size2CC n (a 2CC.2CC.-< cs >-) (s₁ ∷ []) unique-sizes sizes⊆2cc = ℕ.≤-trans (ℕ.≤-reflexive (ℕ.+-comm (2 ^ n) 0)) (2^n≤size2CC-artifact n s₁ a cs (sizes⊆2cc zero))
n*2^n≤size2CC n (a 2CC.2CC.-< cs >-) (s₁ ∷ s₂ ∷ sizes) ((s₁≢s₂ ∷ s₁∉sizes) ∷ unique-sizes) sizes⊆2cc = ⊥-elim
  (impossible-artifact-sizes
    n
    cs
    (List.applyUpTo (artifact n) (suc s₁))
    (List.applyUpTo (artifact n) (suc s₂))
    (λ length-s₁≡length-s₂ → s₁≢s₂ (ℕ.suc-injective (begin
        suc s₁
      ≡⟨ List.length-applyUpTo (artifact n) (suc s₁) ⟨
        List.length (List.applyUpTo (artifact n) (suc s₁))
      ≡⟨ length-s₁≡length-s₂ ⟩
        List.length (List.applyUpTo (artifact n) (suc s₂))
      ≡⟨ List.length-applyUpTo (artifact n) (suc s₂) ⟩
        suc s₂
      ∎)))
    (∈-children n (suc s₁) (List.applyUpTo (artifact n) (suc s₁)) cs (sizes⊆2cc zero))
    (∈-children n (suc s₂) (List.applyUpTo (artifact n) (suc s₂)) cs (sizes⊆2cc (suc zero)))
  )
  where open Eq.≡-Reasoning
n*2^n≤size2CC n (D 2CC.2CC.⟨ l , r ⟩) sizes unique-sizes sizes⊆2cc =
  begin
    List.length sizes * 2 ^ n
  ≤⟨ ℕ.*-monoˡ-≤ (2 ^ n) (split-sizes-length n D l r sizes sizes⊆2cc) ⟩
    (List.length (proj₁ (split-sizes n D l r sizes sizes⊆2cc)) + List.length (proj₂ (split-sizes n D l r sizes sizes⊆2cc))) * 2 ^ n
  ≡⟨ ℕ.*-distribʳ-+ (2 ^ n) (List.length (proj₁ (split-sizes n D l r sizes sizes⊆2cc))) (List.length (proj₂ (split-sizes n D l r sizes sizes⊆2cc))) ⟩
    List.length (proj₁ (split-sizes n D l r sizes sizes⊆2cc)) * 2 ^ n + List.length (proj₂ (split-sizes n D l r sizes sizes⊆2cc)) * 2 ^ n
  ≤⟨ ℕ.+-monoʳ-≤ (List.length (proj₁ (split-sizes n D l r sizes sizes⊆2cc)) * 2 ^ n) (n*2^n≤size2CC n r (proj₂ (split-sizes n D l r sizes sizes⊆2cc)) (List.AllPairs-resp-⊆ (proj₂ (split-sizes-sublist n D l r sizes sizes⊆2cc)) unique-sizes) (proj₂ (split-sizes⊆ n D l r sizes sizes⊆2cc))) ⟩
    List.length (proj₁ (split-sizes n D l r sizes sizes⊆2cc)) * 2 ^ n + size2CC r
  ≤⟨ ℕ.+-monoˡ-≤ (size2CC r) (n*2^n≤size2CC n l (proj₁ (split-sizes n D l r sizes sizes⊆2cc)) (List.AllPairs-resp-⊆ (proj₁ (split-sizes-sublist n D l r sizes sizes⊆2cc)) unique-sizes) (proj₁ (split-sizes⊆ n D l r sizes sizes⊆2cc))) ⟩
    size2CC l + size2CC r
  <⟨ s≤s ℕ.≤-refl ⟩
    suc (size2CC l + size2CC r)
  ≡⟨⟩
    size2CC (D 2CC.2CC.⟨ l , r ⟩)
  ∎
  where
  open ℕ.≤-Reasoning

fst-config : ℕ → ℕ → Bool
fst-config i f = f ℕ.≤ᵇ i

select-applyUpTo-feature :
  ∀ (k n i : ℕ)
  → i ≤ n
  → select (fst-config i) (List.applyUpTo (λ m → m :: feature k m) (suc n))
  ≡ List.applyUpTo (λ m → feature k m) (suc i)
select-applyUpTo-feature k n i i≤n =
  begin
    select (fst-config i) (List.applyUpTo (λ m → m :: feature k m) (suc n))
  ≡⟨ Eq.cong (λ x → select (fst-config i) (List.applyUpTo (λ m → m :: feature k m) (suc x))) (ℕ.m+[n∸m]≡n i≤n) ⟨
    select (fst-config i) (List.applyUpTo (λ m → m :: feature k m) (suc (i + (n ∸ i))))
  ≡⟨⟩
    select (fst-config i) (List.applyUpTo (λ m → m :: feature k m) (suc i + offset))
  ≡⟨ selects-init (suc i) zero refl ⟩
    List.applyUpTo (λ m → feature k m) (suc i)
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

variants⊆fst : ∀ (m : ℕ) → (variant m ∘ suc ∘ List.lookup (List.upTo m)) ⊆ FST.⟦ fst m ⟧
variants⊆fst m size = Prod.map₂ (Eq.trans (Eq.cong (variant m ∘ suc) (List.lookup-upTo m size))) (variant∈fst m (Fin.toℕ size) (ℕ.≤-trans (Fin.toℕ≤n size) (ℕ.≤-reflexive (List.length-upTo m))))

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
      4 + 2 ^ m + 2 * m
    ≤⟨ ℕ.+-monoʳ-≤ (4 + 2 ^ m) (2*n≤2^n m) ⟩
      4 + 2 ^ m + 2 ^ m
    ≤⟨ ℕ.+-monoˡ-≤ (2 ^ m) (ℕ.+-monoˡ-≤ (2 ^ m) (ℕ.m≤m*n 4 (2 ^ m) {{ℕ.>-nonZero (ℕ.m^n>0 2 m)}})) ⟩
      4 * 2 ^ m + 2 ^ m + 2 ^ m
    ≡⟨ Eq.cong (λ x → 4 * 2 ^ m + x + x) (ℕ.*-identityˡ (2 ^ m)) ⟨
      4 * 2 ^ m + 1 * 2 ^ m + 1 * 2 ^ m
    ≡⟨ Eq.cong (_+ 1 * 2 ^ m) (ℕ.*-distribʳ-+ (2 ^ m) 4 1) ⟨
      5 * 2 ^ m + 1 * 2 ^ m
    ≡⟨ ℕ.*-distribʳ-+ (2 ^ m) 5 1 ⟨
      6 * 2 ^ m
    <⟨ ℕ.*-monoˡ-< (2 ^ m) ⦃ ℕ.>-nonZero (ℕ.m^n>0 2 m) ⦄ (ℕ.n<1+n 6) ⟩
      7 * 2 ^ m
    ∎)
  ⟩
    suc n * (7 * 2 ^ m)
  ≡⟨ ℕ.*-assoc (suc n) 7 (2 ^ m) ⟨
    suc n * 7 * 2 ^ m
  ≡⟨ Eq.cong (_* 2 ^ m) (ℕ.*-comm (suc n) 7) ⟩
    7 * suc n * 2 ^ m
  ≡⟨⟩
    m * 2 ^ m
  ≡⟨ Eq.cong (_* 2 ^ m) (List.length-upTo m) ⟨
    List.length (List.upTo m) * 2 ^ m
  ≤⟨ n*2^n≤size2CC m 2cc (List.upTo m) (Unique.upTo⁺ m) (⊆-trans (variants⊆fst m) (proj₁ fst≅2cc)) ⟩
    size2CC 2cc
  ∎
  where
  open ℕ.≤-Reasoning
  m = 7 * suc n
