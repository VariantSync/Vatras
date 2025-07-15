open import Vatras.Framework.Definitions using (𝔽; 𝔸; NAT; atomSize)
-- TODO abstract over (F : 𝔽) using a map (ℕ → 𝔽)
module Vatras.SyntacticExpressiveness.OC≱2CC where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.Nat as ℕ using (ℕ; zero; suc; _≤_; _<_; s≤s; z≤n; _<ᵇ_; _+_; _*_; _^_; _∸_)
import Data.Nat.Properties as ℕ
open import Data.List as List using (List; []; _∷_)
import Data.List.Properties as List
import Data.List.Relation.Binary.Subset.Propositional as Subset
import Data.List.Relation.Binary.Subset.Propositional.Properties as Subset
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Unique.DecPropositional ℕ._≟_ using (Unique; []; _∷_)
import Data.List.Relation.Unary.Unique.DecPropositional.Properties as Unique
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)

open import Function using (_∘_; id)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Reflects using (ofʸ; ofⁿ)
open import Size using (Size; ∞)

import Vatras.Util.List as List
open import Vatras.Data.EqIndexedSet using (_≅_; _∈_; _⊆_)
open import Vatras.Framework.Variants using (Rose; children-equality)
open import Vatras.Framework.Compiler using (LanguageCompiler)
open import Vatras.Lang.All.Fixed ℕ (Rose ∞)
import Vatras.Lang.2CC.ReflectsVariantSize as 2CC
open import Vatras.SyntacticExpressiveness using (_≱Size_)
open import Vatras.SyntacticExpressiveness.Sizes ℕ using (sizeRose; SizedWFOC; sizeWFOC; sizeOC; Sized2CC; size2CC)

options : ℕ → List (OC.OC ∞ NAT)
options zero = []
options (suc n) = n OC.❲ 0 OC.-< [] >- ❳ ∷ options n

oc : ℕ → OC.WFOC ∞ NAT
oc n = OC.Root zero ((2 ^ n) OC.-< [] >- ∷ options n)

size-options : ∀ n → List.sum (List.map sizeOC (options n)) ≡ 2 * n
size-options zero = Eq.refl
size-options (suc n) =
    List.sum (List.map sizeOC (options (suc n)))
  ≡⟨⟩
    suc (suc (List.sum (List.map sizeOC (options n))))
  ≡⟨ Eq.cong (λ x → suc (suc x)) (size-options n) ⟩
    suc (suc (2 * n))
  ≡⟨ ℕ.*-suc 2 n ⟨
    2 * (suc n)
  ∎
  where
  open Eq.≡-Reasoning

size-oc : ∀ (n : ℕ) → sizeWFOC (oc n) ≡ 2 ^ n + 2 * suc n
size-oc n =
    sizeWFOC (oc n)
  ≡⟨⟩
    1 + List.sum (List.map sizeOC ((2 ^ n) OC.-< [] >- ∷ options n))
  ≡⟨⟩
    1 + sizeOC {A = NAT} ((2 ^ n) OC.-< [] >-) + List.sum (List.map sizeOC (options n))
  ≡⟨⟩
    2 + atomSize NAT (2 ^ n) + 0 + List.sum (List.map sizeOC (options n))
  ≡⟨⟩
    2 + (2 ^ n + 0) + List.sum (List.map sizeOC (options n))
  ≡⟨ Eq.cong (λ x → 2 + (2 ^ n + 0) + x) (size-options n) ⟩
    2 + (2 ^ n + 0) + 2 * n
  ≡⟨ Eq.cong (λ x → 2 + x + 2 * n) (ℕ.+-identityʳ (2 ^ n)) ⟩
    2 + 2 ^ n + 2 * n
  ≡⟨ Eq.cong (_+ 2 * n) (ℕ.+-comm 2 (2 ^ n)) ⟩
    2 ^ n + 2 + 2 * n
  ≡⟨ ℕ.+-assoc (2 ^ n) 2 (2 * n) ⟩
    2 ^ n + (2 + 2 * n)
  ≡⟨ Eq.cong (2 ^ n +_) (ℕ.*-suc 2 n) ⟨
    2 ^ n + 2 * suc n
  ∎
  where
  open Eq.≡-Reasoning

exponential-artifact : ℕ → Rose ∞ NAT
exponential-artifact n = (2 ^ n) Rose.-< [] >-

variant-cs : ℕ → List (Rose ∞ NAT)
variant-cs i = List.replicate i (0 Rose.-< [] >-)

variant : ℕ → ℕ → Rose ∞ NAT
variant n i = 0 Rose.-< exponential-artifact n ∷ variant-cs i >-

variant∈e⇒length-cs
  : ∀ {i} (n l : ℕ) (a : ℕ) (cs : List (2CC.2CC i NAT))
  → variant n l ∈ 2CC.⟦ a 2CC.-< cs >- ⟧
  → List.length cs ≡ suc l
variant∈e⇒length-cs n l a cs (c , v≡e) =
    List.length cs
  ≡⟨ List.length-map (λ e → 2CC.⟦ e ⟧ c) cs ⟨
    List.length (List.map (λ e → 2CC.⟦ e ⟧ c) cs)
  ≡⟨ Eq.cong List.length (children-equality v≡e) ⟨
    List.length (exponential-artifact n ∷ variant-cs l)
  ≡⟨⟩
    suc (List.length (variant-cs l))
  ≡⟨ Eq.cong suc (List.length-replicate l) ⟩
    suc l
  ∎
  where
  open Eq.≡-Reasoning

variant-size
  : (n l : ℕ)
  → 2 ^ n < sizeRose (variant n l)
variant-size n l =
  begin-strict
    2 ^ n
  ≡⟨ ℕ.+-identityʳ (2 ^ n) ⟨
    2 ^ n + 0
  ≤⟨ ℕ.m≤m+n (2 ^ n + 0) _ ⟩
    2 ^ n + 0 + List.sum (List.map sizeRose (variant-cs l))
  <⟨ ℕ.m<n+m (2 ^ n + 0 + List.sum (List.map sizeRose (variant-cs l))) {2} (s≤s z≤n) ⟩
    2 + (2 ^ n + 0 + List.sum (List.map sizeRose (variant-cs l)))
  ≡⟨⟩
    1 + (sizeRose (exponential-artifact n) + List.sum (List.map sizeRose (variant-cs l)))
  ≡⟨⟩
    sizeRose (variant n l)
  ∎
  where
  open ℕ.≤-Reasoning

partition : ∀ {i : Size} (n D : ℕ)
  → (c₁ c₂ : 2CC.2CC i NAT)
  → (ls : List ℕ)
  → Unique ls
  → All (λ l → variant n l ∈ 2CC.⟦ D 2CC.⟨ c₁ , c₂ ⟩ ⟧) ls
  → ∃[ ls₁ ] ∃[ ls₂ ]
    ls₁ Subset.⊆ ls × ls₂ Subset.⊆ ls
  × List.length ls₁ + List.length ls₂ ≡ List.length ls
  × Unique ls₁ × All (λ l → variant n l ∈ 2CC.⟦ c₁ ⟧) ls₁
  × Unique ls₂ × All (λ l → variant n l ∈ 2CC.⟦ c₂ ⟧) ls₂
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

big : ∀ {i : Size} (n : ℕ)
  → (2cc : 2CC.2CC i NAT)
  → (ls : List ℕ)
  → Unique ls
  → All (λ l → variant n l ∈ 2CC.⟦ 2cc ⟧) ls
  → List.length ls * 2 ^ n < size2CC 2cc
big n (a 2CC.-< cs >-) [] unique-ls all-∈ = s≤s z≤n
big n (a 2CC.-< cs >-) (l₁ ∷ []) unique-ls all-∈ =
  begin-strict
    1 * 2 ^ n
  ≡⟨ ℕ.*-identityˡ (2 ^ n) ⟩
    2 ^ n
  <⟨ variant-size n l₁ ⟩
    sizeRose (variant n l₁)
  ≤⟨ 2CC.reflectsVariantSize (variant n l₁) (a 2CC.-< cs >-) (All.lookup all-∈ (here Eq.refl)) ⟩
    size2CC (a 2CC.2CC.-< cs >-)
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

conf : ℕ → OC.Configuration
conf n i = i <ᵇ n

⟦options⟧-tail : ∀ n l
  → n ≤ l
  → List.catMaybes (List.map (λ e → OC.⟦ e ⟧ₒ (conf l)) (options n))
  ≡ variant-cs n
⟦options⟧-tail zero l n≤l = Eq.refl
⟦options⟧-tail (suc n) l n<l with ℕ.<ᵇ-reflects-< n l
⟦options⟧-tail (suc n) l n<l | reflects-n<l with n <ᵇ l
⟦options⟧-tail (suc n) l n<l | ofʸ n<l' | .true =
  Eq.cong (0 Rose.-< [] >- ∷_) (⟦options⟧-tail n l (ℕ.<⇒≤ n<l))
⟦options⟧-tail (suc n) l n<l | ofⁿ n≮l | .false = ⊥-elim (n≮l n<l)

⟦options⟧ : ∀ n l
  → l ≤ n
  → List.catMaybes (List.map (λ e → OC.⟦ e ⟧ₒ (conf l)) (options n))
  ≡ variant-cs l
⟦options⟧ zero .zero z≤n = Eq.refl
⟦options⟧ (suc n) l l≤n with n ℕ.<? l
⟦options⟧ (suc n) l l≤n | no n≮l with n ℕ.<ᵇ l | ℕ.<ᵇ-reflects-< n l
⟦options⟧ (suc n) l l≤n | no n≮l | .false | ofⁿ n≮l' = ⟦options⟧ n l (ℕ.≮⇒≥ n≮l)
⟦options⟧ (suc n) l l≤n | no n≮l | .true | ofʸ n<l = ⊥-elim (n≮l n<l)
⟦options⟧ (suc n) l l≤n | yes n<l =
    List.catMaybes (List.map (λ e → OC.⟦ e ⟧ₒ (conf l)) (options (suc n)))
  ≡⟨ ⟦options⟧-tail (suc n) l n<l ⟩
    variant-cs (suc n)
  ≡⟨ Eq.cong variant-cs (ℕ.≤∧≮⇒≡ n<l (ℕ.≤⇒≯ l≤n)) ⟩
    variant-cs l
  ∎
  where
  open Eq.≡-Reasoning

⟦oc⟧ : ∀ n l → l ≤ n → OC.⟦ oc n ⟧ (conf l) ≡ variant n l
⟦oc⟧ n l l≤n =
    OC.⟦ oc n ⟧ (conf l)
  ≡⟨⟩
    0 Rose.-< OC.⟦ (2 ^ n) OC.-< [] >- ∷ options n ⟧ₒ-recurse (conf l) >-
  ≡⟨⟩
    0 Rose.-< exponential-artifact n ∷ OC.⟦ options n ⟧ₒ-recurse (conf l) >-
  ≡⟨ Eq.cong (λ x → 0 Rose.-< exponential-artifact n ∷ x >-) (⟦options⟧ n l l≤n) ⟩
    0 Rose.-< exponential-artifact n ∷ variant-cs l >-
  ≡⟨⟩
    variant n l
  ∎
  where
  open Eq.≡-Reasoning

⊆⇒All∈ : ∀ {i} n l
  → l ≤ suc n
  → (2cc : 2CC.2CC i NAT)
  → OC.⟦ oc n ⟧ ⊆ 2CC.⟦ 2cc ⟧
  → All (λ l → variant n l ∈ 2CC.⟦ 2cc ⟧) (List.upTo l)
⊆⇒All∈ n zero l≤n 2cc oc⊆2cc = []
⊆⇒All∈ n (suc l) (s≤s l≤n) 2cc oc⊆2cc =
  Eq.subst
    (All (λ l → variant n l ∈ 2CC.⟦ 2cc ⟧))
    (List.applyUpTo-∷ʳ⁺ id l)
    (All.∷ʳ⁺
      (⊆⇒All∈ n l (ℕ.<⇒≤ (s≤s l≤n)) 2cc oc⊆2cc)
      (Eq.subst
        (_∈ 2CC.⟦ 2cc ⟧)
        (⟦oc⟧ n l l≤n)
        (oc⊆2cc (conf l))))

4*n<16^n : ∀ n → 4 * n < 16 ^ n
4*n<16^n zero = s≤s z≤n
4*n<16^n (suc n) =
  begin-strict
    4 * suc n
  ≡⟨ ℕ.*-suc 4 n ⟩
    4 + 4 * n
  <⟨ ℕ.+-mono-< (s≤s (s≤s (s≤s (s≤s (s≤s z≤n))))) (4*n<16^n n) ⟩
    15 + 16 ^ n
  ≤⟨ ℕ.+-monoˡ-≤ (16 ^ n) (ℕ.*-monoʳ-≤ 15 (ℕ.m^n>0 16 n)) ⟩
    15 * 16 ^ n + 16 ^ n
  ≡⟨ Eq.cong (15 * 16 ^ n +_) (ℕ.+-identityʳ (16 ^ n)) ⟨
    15 * 16 ^ n + (16 ^ n + 0)
  ≡⟨ ℕ.*-distribʳ-+ (16 ^ n) 15 1 ⟨
    16 * 16 ^ n
  ≡⟨⟩
    16 ^ suc n
  ∎
  where
  open ℕ.≤-Reasoning

size2CC>0 : ∀ {i} (2cc : 2CC.2CC i NAT) → 0 < size2CC 2cc
size2CC>0 (a 2CC.-< cs >-) = s≤s z≤n
size2CC>0 (D 2CC.⟨ l , r ⟩) = s≤s z≤n

goal : ∀ {i} (n : ℕ) (2cc : 2CC.2CC i NAT)
  → OC.⟦ oc (4 * n) ⟧ ≅ 2CC.⟦ 2cc ⟧
  → n * sizeWFOC (oc (4 * n)) < size2CC 2cc
goal zero 2cc 2cc≅oc = size2CC>0 2cc
goal n@(suc n-1) 2cc (oc⊆2cc , 2cc⊆oc) =
  begin-strict
    n * sizeWFOC (oc (4 * n))
  ≡⟨ Eq.cong (n *_) (size-oc (4 * n)) ⟩
    n * (2 ^ (4 * n) + 2 * suc (4 * n))
  ≤⟨ ℕ.*-monoʳ-≤ n (ℕ.+-monoʳ-≤ (2 ^ (4 * n)) (ℕ.*-monoʳ-≤ 2 (4*n<16^n n))) ⟩
    n * (2 ^ (4 * n) + 2 * 16 ^ n)
  ≡⟨ Eq.cong (λ x → n * (2 ^ (4 * n) + 2 * x)) (ℕ.^-*-assoc 2 4 n) ⟩
    n * (2 ^ (4 * n) + 2 * 2 ^ (4 * n))
  ≡⟨⟩
    n * (3 * 2 ^ (4 * n))
  <⟨ ℕ.*-monoʳ-< n (ℕ.*-monoˡ-< (2 ^ (4 * n)) {{ℕ.>-nonZero (ℕ.m^n>0 2 (4 * n))}} (ℕ.n<1+n 3)) ⟩
    n * (4 * 2 ^ (4 * n))
  ≡⟨ ℕ.*-assoc n 4 (2 ^ (4 * n)) ⟨
    n * 4 * 2 ^ (4 * n)
  ≡⟨ Eq.cong (_* 2 ^ (4 * n)) (ℕ.*-comm n 4) ⟩
    4 * n * 2 ^ (4 * n)
  <⟨ ℕ.*-monoˡ-< (2 ^ (4 * n)) {{ℕ.>-nonZero (ℕ.m^n>0 2 (4 * n))}} (ℕ.n<1+n (4 * n)) ⟩
    suc (4 * n) * 2 ^ (4 * n)
  ≡⟨ Eq.cong (_* 2 ^ (4 * n)) (List.length-upTo (suc (4 * n))) ⟨
    List.length (List.upTo (suc (4 * n))) * 2 ^ (4 * n)
  <⟨ big
      (4 * n)
      2cc
      (List.upTo (suc (4 * n)))
      (Unique.applyUpTo⁺₁ id (suc (4 * n)) (λ i<j j<n → ℕ.<⇒≢ i<j))
      (⊆⇒All∈ (4 * n) (suc (4 * n)) ℕ.≤-refl 2cc oc⊆2cc)
  ⟩
    size2CC 2cc
  ∎
  where
  open ℕ.≤-Reasoning

OC≱2CC : SizedWFOC ≱Size Sized2CC
OC≱2CC n = NAT , oc (4 * n) , λ 2cc oc≅2cc → goal n 2cc oc≅2cc
