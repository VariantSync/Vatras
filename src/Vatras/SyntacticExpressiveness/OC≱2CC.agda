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
import Data.List.Relation.Unary.AllPairs as AllPairs
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.Unique.DecPropositional ℕ._≟_ using (Unique; []; _∷_)
import Data.List.Relation.Unary.Unique.DecPropositional.Properties as Unique
open import Data.Maybe using (just)
open import Data.Product using (_×_; _,_; proj₁; proj₂; ∃-syntax)

open import Function using (_∘_; id; const)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Nullary.Reflects using (ofʸ; ofⁿ)
open import Size using (Size; ∞)

open import Vatras.Util.AuxProofs using (m∸n<m)
import Vatras.Util.List as List
open import Vatras.Data.EqIndexedSet using (_≅_; _∈_; _⊆_)
open import Vatras.Framework.Variants using (Rose; children-equality)
open import Vatras.Framework.Compiler using (LanguageCompiler)
open import Vatras.Lang.All.Fixed ℕ (Rose ∞)
import Vatras.Lang.2CC.ReflectsVariantSize as 2CC
open import Vatras.Lang.2CC.FixedArtifactLength ℕ NAT using (_≉_; unique-lengths⇒m*sizeRose≤size2CC)
open import Vatras.SyntacticExpressiveness using (_≱Size_)
open import Vatras.SyntacticExpressiveness.Sizes ℕ using (sizeRose; SizedWFOC; sizeWFOC; sizeOC; Sized2CC; size2CC; size2CC>0)

options : ℕ → List (OC.OC ∞ NAT)
options zero = []
options (suc n) = n OC.❲ (0 , 0) OC.-< [] >- ❳ ∷ options n

oc : ℕ → OC.WFOC ∞ NAT
oc n = OC.Root (0 , 0) ((0 , 2 ^ n) OC.-< [] >- ∷ options n)

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
    1 + List.sum (List.map sizeOC ((0 , 2 ^ n) OC.-< [] >- ∷ options n))
  ≡⟨⟩
    1 + sizeOC {A = NAT} ((0 , 2 ^ n) OC.-< [] >-) + List.sum (List.map sizeOC (options n))
  ≡⟨⟩
    2 + atomSize NAT (0 , 2 ^ n) + 0 + List.sum (List.map sizeOC (options n))
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
exponential-artifact n = (0 , 2 ^ n) Rose.-< [] >-

variant-cs : ℕ → List (Rose ∞ NAT)
variant-cs i = List.replicate i ((0 , 0) Rose.-< [] >-)

variant : ℕ → ℕ → Rose ∞ NAT
variant n i = (0 , 0) Rose.-< exponential-artifact n ∷ variant-cs i >-

size-variant
  : (n l : ℕ)
  → 2 ^ n ≤ sizeRose (variant n l)
size-variant n l =
  begin
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

variant-≉ : ∀ n {l₁} {l₂} → l₁ ≢ l₂ → variant n l₁ ≉ variant n l₂
variant-≉ n {l₁} {l₂} l₁≢l₂ v₁≡v₂ = l₁≢l₂ (
    l₁
  ≡⟨ List.length-replicate l₁ ⟨
    List.length (variant-cs l₁)
  ≡⟨ ℕ.suc-injective v₁≡v₂ ⟩
    List.length (variant-cs l₂)
  ≡⟨ List.length-replicate l₂ ⟩
    l₂
  ∎)
  where
  open Eq.≡-Reasoning

config : ℕ → OC.Configuration
config n i = i <ᵇ n

⟦options⟧-tail : ∀ n l
  → n ≤ l
  → List.catMaybes (List.map (λ e → OC.⟦ e ⟧ₒ (config l)) (options n))
  ≡ variant-cs n
⟦options⟧-tail zero l n≤l = Eq.refl
⟦options⟧-tail (suc n) l n<l with ℕ.<ᵇ-reflects-< n l
⟦options⟧-tail (suc n) l n<l | reflects-n<l with n <ᵇ l
⟦options⟧-tail (suc n) l n<l | ofʸ n<l' | .true =
  Eq.cong ((0 , 0) Rose.-< [] >- ∷_) (⟦options⟧-tail n l (ℕ.<⇒≤ n<l))
⟦options⟧-tail (suc n) l n<l | ofⁿ n≮l | .false = ⊥-elim (n≮l n<l)

⟦options⟧ : ∀ n l
  → l ≤ n
  → List.catMaybes (List.map (λ e → OC.⟦ e ⟧ₒ (config l)) (options n))
  ≡ variant-cs l
⟦options⟧ zero .zero z≤n = Eq.refl
⟦options⟧ (suc n) l l≤n with n ℕ.<? l
⟦options⟧ (suc n) l l≤n | no n≮l with n ℕ.<ᵇ l | ℕ.<ᵇ-reflects-< n l
⟦options⟧ (suc n) l l≤n | no n≮l | .false | ofⁿ n≮l' = ⟦options⟧ n l (ℕ.≮⇒≥ n≮l)
⟦options⟧ (suc n) l l≤n | no n≮l | .true | ofʸ n<l = ⊥-elim (n≮l n<l)
⟦options⟧ (suc n) l l≤n | yes n<l =
    List.catMaybes (List.map (λ e → OC.⟦ e ⟧ₒ (config l)) (options (suc n)))
  ≡⟨ ⟦options⟧-tail (suc n) l n<l ⟩
    variant-cs (suc n)
  ≡⟨ Eq.cong variant-cs (ℕ.≤∧≮⇒≡ n<l (ℕ.≤⇒≯ l≤n)) ⟩
    variant-cs l
  ∎
  where
  open Eq.≡-Reasoning

⟦oc⟧ : ∀ n l → l ≤ n → OC.⟦ oc n ⟧ (config l) ≡ variant n l
⟦oc⟧ n l l≤n =
    OC.⟦ oc n ⟧ (config l)
  ≡⟨⟩
    (0 , 0) Rose.-< OC.⟦ (0 , 2 ^ n) OC.-< [] >- ∷ options n ⟧ₒ-recurse (config l) >-
  ≡⟨⟩
    (0 , 0) Rose.-< exponential-artifact n ∷ OC.⟦ options n ⟧ₒ-recurse (config l) >-
  ≡⟨ Eq.cong (λ x → (0 , 0) Rose.-< exponential-artifact n ∷ x >-) (⟦options⟧ n l l≤n) ⟩
    (0 , 0) Rose.-< exponential-artifact n ∷ variant-cs l >-
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
        (oc⊆2cc (config l))))

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

goal : ∀ {i} (n : ℕ) (2cc : 2CC.2CC i NAT)
  → OC.⟦ oc (4 * n) ⟧ ≅ 2CC.⟦ 2cc ⟧
  → n * sizeWFOC (oc (4 * n)) < size2CC 2cc
goal zero 2cc 2cc≅oc = size2CC>0 2cc
goal n@(suc n-1) 2cc (oc⊆2cc , 2cc⊆oc) =
  begin-strict
    n * sizeWFOC (oc m)
  ≡⟨ Eq.cong (n *_) (size-oc m) ⟩
    n * (2 ^ m + 2 * suc m)
  ≤⟨ ℕ.*-monoʳ-≤ n (ℕ.+-monoʳ-≤ (2 ^ m) (ℕ.*-monoʳ-≤ 2 (4*n<16^n n))) ⟩
    n * (2 ^ m + 2 * 16 ^ n)
  ≡⟨ Eq.cong (λ x → n * (2 ^ m + 2 * x)) (ℕ.^-*-assoc 2 4 n) ⟩
    n * (2 ^ m + 2 * 2 ^ m)
  ≡⟨⟩
    n * (3 * 2 ^ m)
  <⟨ ℕ.*-monoʳ-< n (ℕ.*-monoˡ-< (2 ^ m) {{ℕ.>-nonZero (ℕ.m^n>0 2 m)}} (ℕ.n<1+n 3)) ⟩
    n * (4 * 2 ^ m)
  ≡⟨ ℕ.*-assoc n 4 (2 ^ m) ⟨
    n * 4 * 2 ^ m
  ≡⟨ Eq.cong (_* 2 ^ m) (ℕ.*-comm n 4) ⟩
    m * 2 ^ m
  <⟨ ℕ.*-monoˡ-< (2 ^ m) {{ℕ.>-nonZero (ℕ.m^n>0 2 m)}} (ℕ.n<1+n m) ⟩
    suc m * 2 ^ m
  ≡⟨ Eq.cong (_* 2 ^ m) (List.length-upTo (suc m)) ⟨
    List.length (List.upTo (suc m)) * 2 ^ m
  ≤⟨ unique-lengths⇒m*sizeRose≤size2CC
       (2 ^ m)
       2cc
       (List.upTo (suc m))
       (variant m)
       (size-variant m)
       (variant-≉ (suc m))
       (Unique.applyUpTo⁺₁ id (suc m) (λ i<j j<n → ℕ.<⇒≢ i<j))
       (⊆⇒All∈ m (suc m) ℕ.≤-refl 2cc oc⊆2cc)
  ⟩
    size2CC 2cc
  ∎
  where
  open ℕ.≤-Reasoning
  m = 4 * n

OC≱2CC : SizedWFOC ≱Size Sized2CC
OC≱2CC n = NAT , oc (4 * n) , λ 2cc oc≅2cc → goal n 2cc oc≅2cc
