open import Vatras.Framework.Definitions using (𝔽; 𝔸; NAT)
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
open import Vatras.Framework.Variants using (Rose; Rose-injective)
open import Vatras.Framework.Compiler using (LanguageCompiler)
open import Vatras.Lang.All.Fixed ℕ (Rose ∞)
open import Vatras.SyntacticExpressiveness using (_≱Size_)
open import Vatras.SyntacticExpressiveness.Sizes ℕ using (SizedWFOC; sizeWFOC; sizeOC; Sized2CC; size2CC)

options : ℕ → List (OC.OC ∞ NAT)
options zero = []
options (suc n) = n OC.❲ suc n OC.-< [] >- ❳ ∷ options n

exponential-oc : ℕ → OC.OC ∞ NAT
exponential-oc zero = 0 OC.-< [] >-
exponential-oc (suc n) = 0 OC.-< exponential-oc n ∷ exponential-oc n ∷ [] >-

oc : ℕ → OC.WFOC ∞ NAT
oc n = OC.Root zero (exponential-oc n ∷ options n)

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

size-exponential-artifact : ∀ (n : ℕ) → sizeOC (exponential-oc n) ≡ 2 ^ (suc n) ∸ 1
size-exponential-artifact zero = Eq.refl
size-exponential-artifact (suc n) =
    sizeOC (exponential-oc (suc n))
  ≡⟨⟩
    sizeOC (0 OC.-< exponential-oc n ∷ exponential-oc n ∷ [] >-)
  ≡⟨⟩
    suc (sizeOC (exponential-oc n) + (sizeOC (exponential-oc n) + 0))
  ≡⟨ Eq.cong (λ x → suc (x + (x + 0))) (size-exponential-artifact n) ⟩
    suc (2 ^ (suc n) ∸ 1 + (2 ^ (suc n) ∸ 1 + 0))
  ≡⟨⟩
    suc (2 ^ (suc n) ∸ 1) + (2 ^ (suc n) ∸ 1 + 0)
  ≡⟨ Eq.cong (λ x → suc (2 ^ (suc n) ∸ 1) + x) (ℕ.+-identityʳ (2 ^ (suc n) ∸ 1)) ⟩
    suc (2 ^ (suc n) ∸ 1) + (2 ^ (suc n) ∸ 1)
  ≡⟨ Eq.cong (_+ (2 ^ (suc n) ∸ 1)) (ℕ.+-∸-assoc 1 (ℕ.m^n>0 2 (suc n))) ⟨
    2 ^ (suc n) + (2 ^ (suc n) ∸ 1)
  ≡⟨ ℕ.+-∸-assoc (2 ^ (suc n)) {2 ^ (suc n)} {1} (ℕ.m^n>0 2 (suc n)) ⟨
    (2 ^ (suc n) + 2 ^ (suc n)) ∸ 1
  ≡⟨ Eq.cong (λ x → 2 ^ (suc n) + x ∸ 1) (ℕ.+-identityʳ (2 ^ (suc n))) ⟨
    2 ^ (suc (suc n)) ∸ 1
  ∎
  where
  open Eq.≡-Reasoning

size-oc : ∀ (n : ℕ) → sizeWFOC (oc n) ≡ 2 ^ (suc n) + 2 * n
size-oc n =
    sizeWFOC (oc n)
  ≡⟨⟩
    suc (sizeOC (exponential-oc n) + List.sum (List.map sizeOC (options n)))
  ≡⟨ Eq.cong₂ (λ x y → suc (x + y)) (size-exponential-artifact n) (size-options n) ⟩
    suc (2 ^ (suc n) ∸ 1 + 2 * n)
  ≡⟨ Eq.cong (_+ 2 * n) (ℕ.+-∸-assoc 1 (ℕ.m^n>0 2 (suc n))) ⟨
    2 ^ (suc n) + 2 * n
  ∎
  where
  open Eq.≡-Reasoning

exponential-artifact : ℕ → Rose ∞ NAT
exponential-artifact zero = 0 Rose.-< [] >-
exponential-artifact (suc n) = 0 Rose.-< exponential-artifact n ∷ exponential-artifact n ∷ [] >-

variant-cs : ℕ → List (Rose ∞ NAT)
variant-cs zero = []
variant-cs (suc i) = suc i Rose.-< [] >- ∷ variant-cs i

variant : ℕ → ℕ → Rose ∞ NAT
variant n i = 0 Rose.-< exponential-artifact n ∷ variant-cs i >-

length-variants-cs : ∀ n → List.length (variant-cs n) ≡ n
length-variants-cs zero = Eq.refl
length-variants-cs (suc n) = Eq.cong suc (length-variants-cs n)

variant∈e⇒length-cs
  : ∀ {i} (n l : ℕ) (a : ℕ) (cs : List (2CC.2CC i NAT))
  → variant n l ∈ 2CC.⟦ a 2CC.-< cs >- ⟧
  → List.length cs ≡ suc l
variant∈e⇒length-cs n l a cs (c , v≡e) =
    List.length cs
  ≡⟨ List.length-map (λ e → 2CC.⟦ e ⟧ c) cs ⟨
    List.length (List.map (λ e → 2CC.⟦ e ⟧ c) cs)
  ≡⟨ Eq.cong List.length (proj₂ (Rose-injective v≡e)) ⟨
    List.length (exponential-artifact n ∷ variant-cs l)
  ≡⟨ Eq.cong suc (length-variants-cs l) ⟩
    suc l
  ∎
  where
  open Eq.≡-Reasoning

exponential-artifact∈e⇒length-cs
  : ∀ {i} (n : ℕ) (a : ℕ) (cs : List (2CC.2CC i NAT))
  → exponential-artifact (suc n) ∈ 2CC.⟦ a 2CC.-< cs >- ⟧
  → List.length cs ≡ 2
exponential-artifact∈e⇒length-cs n a cs (c , v≡e) =
    List.length cs
  ≡⟨ List.length-map (λ e → 2CC.⟦ e ⟧ c) cs ⟨
    List.length (List.map (λ e → 2CC.⟦ e ⟧ c) cs)
  ≡⟨ Eq.cong List.length (proj₂ (Rose-injective v≡e)) ⟨
    List.length (exponential-artifact n ∷ exponential-artifact n ∷ [])
  ≡⟨⟩
    2
  ∎
  where
  open Eq.≡-Reasoning

exponential-big
  : ∀ {i : Size} (n l : ℕ)
  → (2cc : 2CC.2CC i NAT)
  → exponential-artifact n ∈ 2CC.⟦ 2cc ⟧
  → 2 ^ (suc n) ∸ 1 ≤ size2CC 2cc
exponential-big n l (D 2CC.⟨ c₁ , c₂ ⟩) (c , v≡2cc) with c D
exponential-big n l (D 2CC.⟨ c₁ , c₂ ⟩) (c , v≡2cc) | true = ℕ.≤-trans (exponential-big n l c₁ (c , v≡2cc)) (ℕ.≤-trans (ℕ.m≤m+n (size2CC c₁) (size2CC c₂)) (ℕ.m≤n+m (size2CC c₁ + size2CC c₂) 1))
exponential-big n l (D 2CC.⟨ c₁ , c₂ ⟩) (c , v≡2cc) | false = ℕ.≤-trans (exponential-big n l c₂ (c , v≡2cc)) (ℕ.m≤n+m (size2CC c₂) (suc (size2CC c₁)))
exponential-big zero l (a 2CC.-< cs >-) (c , v≡2cc) = s≤s z≤n
exponential-big (suc n) l (a 2CC.-< cs >-) (c , v≡2cc) with exponential-artifact∈e⇒length-cs n a cs (c , v≡2cc)
exponential-big (suc n) l (a 2CC.-< c₁ ∷ c₂ ∷ [] >-) (c , v≡2cc) | Eq.refl =
  begin
    2 ^ (suc (suc n)) ∸ 1
  ≡⟨ Eq.cong (λ x → (2 ^ (suc n) + x) ∸ 1) (ℕ.+-identityʳ (2 ^ (suc n))) ⟩
    (2 ^ (suc n) + 2 ^ (suc n)) ∸ 1
  ≡⟨ ℕ.+-∸-assoc (2 ^ (suc n)) (ℕ.m^n>0 2 (suc n)) ⟩
    2 ^ (suc n) + (2 ^ (suc n) ∸ 1)
  ≡⟨ ℕ.+-∸-assoc 1 (ℕ.≤-trans (ℕ.m^n>0 2 (suc n)) (ℕ.m≤m+n (2 ^ (suc n)) (2 ^ (suc n) ∸ 1))) ⟩
    1 + ((2 ^ (suc n) + (2 ^ (suc n) ∸ 1)) ∸ 1)
  ≡⟨ Eq.cong suc (ℕ.+-∸-comm (2 ^ suc n ∸ 1) (ℕ.m^n>0 2 (suc n))) ⟩
    suc ((2 ^ (suc n) ∸ 1) + (2 ^ (suc n) ∸ 1))
  ≤⟨ s≤s (ℕ.+-mono-≤ (exponential-big n l c₁ (c , proj₁ (List.∷-injective (proj₂ (Rose-injective v≡2cc))))) (exponential-big n l c₂ (c , proj₁ (List.∷-injective (proj₂ (List.∷-injective (proj₂ (Rose-injective v≡2cc)))))))) ⟩
    suc (size2CC c₁ + size2CC c₂)
  ≡⟨ Eq.cong (λ x → suc (size2CC c₁ + x)) (ℕ.+-identityʳ (size2CC c₂)) ⟨
    suc (size2CC c₁ + (size2CC c₂ + 0))
  ≡⟨⟩
    size2CC (a 2CC.-< c₁ ∷ c₂ ∷ [] >-)
  ∎
  where
  open ℕ.≤-Reasoning

exponentially-big
  : ∀ {i : Size} (n l : ℕ)
  → (2cc : 2CC.2CC i NAT)
  → variant n l ∈ 2CC.⟦ 2cc ⟧
  → 2 ^ n < size2CC 2cc
exponentially-big n l (D 2CC.⟨ c₁ , c₂ ⟩) (c , v≡2cc) with c D
exponentially-big n l (D 2CC.⟨ c₁ , c₂ ⟩) (c , v≡2cc) | true = ℕ.≤-trans (exponentially-big n l c₁ (c , v≡2cc)) (ℕ.≤-trans (ℕ.m≤m+n (size2CC c₁) (size2CC c₂)) (ℕ.m≤n+m (size2CC c₁ + size2CC c₂) 1))
exponentially-big n l (D 2CC.⟨ c₁ , c₂ ⟩) (c , v≡2cc) | false =  ℕ.≤-trans (exponentially-big n l c₂ (c , v≡2cc)) (ℕ.m≤n+m (size2CC c₂) (suc (size2CC c₁)))
exponentially-big n l (a 2CC.-< cs >-) (c , v≡2cc) with variant∈e⇒length-cs n l a cs (c , v≡2cc)
exponentially-big n l (a 2CC.-< c₁ ∷ cs >-) (c , v≡2cc) | Eq.refl =
  begin-strict
    2 ^ n
  <⟨ ℕ.m<m+n (2 ^ n) (ℕ.m^n>0 2 n) ⟩
    2 ^ n + 2 ^ n
  ≡⟨ Eq.cong (2 ^ n +_) (ℕ.+-identityʳ (2 ^ n)) ⟨
    2 ^ n + (2 ^ n + 0)
  ≡⟨⟩
    2 ^ (suc n)
  ≡⟨ ℕ.+-∸-assoc 1 (ℕ.m^n>0 2 (suc n)) ⟩
    suc (2 ^ (suc n) ∸ 1)
  ≤⟨ s≤s (exponential-big n l c₁ (c , proj₁ (List.∷-injective (proj₂ (Rose-injective v≡2cc))))) ⟩
    suc (size2CC c₁)
  ≤⟨ ℕ.m≤m+n (suc (size2CC c₁)) (List.sum (List.map size2CC cs)) ⟩
    suc (size2CC c₁ + List.sum (List.map size2CC cs))
  ≡⟨⟩
    size2CC (a 2CC.2CC.-< c₁ ∷ cs >-)
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
partition n D c₁ c₂ [] unique-ls ls⊆2cc = [] , [] , Subset.⊆-refl , Subset.⊆-refl , Eq.refl , [] , [] , [] , []
partition n D c₁ c₂ (l ∷ ls) (l∉ls ∷ unique-ls) ((c , l≡2cc) ∷ ls⊆2cc) with c D | partition n D c₁ c₂ ls unique-ls ls⊆2cc
partition n D c₁ c₂ (l ∷ ls) (l∉ls ∷ unique-ls) ((c , l≡2cc) ∷ ls⊆2cc) | true | ls₁ , ls₂ , ls₁⊆ls , ls₂⊆ls , ls₁+ls₂≡ls , unique-ls₁ , ls₁∈l , unique-ls₂ , ls₂∈r =
  l ∷ ls₁ , ls₂ , Subset.∷⁺ʳ l ls₁⊆ls , there ∘ ls₂⊆ls , Eq.cong suc ls₁+ls₂≡ls , All.anti-mono ls₁⊆ls l∉ls ∷ unique-ls₁ , (c , l≡2cc) ∷ ls₁∈l , unique-ls₂ , ls₂∈r
partition n D c₁ c₂ (l ∷ ls) (l∉ls ∷ unique-ls) ((c , l≡2cc) ∷ ls⊆2cc) | false | ls₁ , ls₂ , ls₁⊆ls , ls₂⊆ls , ls₁+ls₂≡ls , unique-ls₁ , ls₁∈l , unique-ls₂ , ls₂∈r =
  ls₁ , l ∷ ls₂ , there ∘ ls₁⊆ls , Subset.∷⁺ʳ l ls₂⊆ls , Eq.trans (ℕ.+-suc (List.length ls₁) (List.length ls₂)) (Eq.cong suc ls₁+ls₂≡ls) , unique-ls₁ , ls₁∈l , All.anti-mono ls₂⊆ls l∉ls ∷ unique-ls₂ , (c , l≡2cc) ∷ ls₂∈r

big : ∀ {i : Size} (n : ℕ)
  → (2cc : 2CC.2CC i NAT)
  → (ls : List ℕ)
  → Unique ls
  → All (λ l → variant n l ∈ 2CC.⟦ 2cc ⟧) ls
  → List.length ls * 2 ^ n < size2CC 2cc
big n (a 2CC.-< cs >-) [] unique-ls all-∈ = s≤s z≤n
big n (a 2CC.-< cs >-) (l₁ ∷ []) unique-ls all-∈ = Eq.subst (_< size2CC (a 2CC.-< cs >-)) (Eq.sym (ℕ.+-identityʳ (2 ^ n))) (exponentially-big n l₁ (a 2CC.-< cs >-) (All.lookup all-∈ (here Eq.refl)))
big n (a 2CC.-< cs >-) (l₁ ∷ l₂ ∷ ls) ((l₁≢l₂ ∷ l₁∉ls) ∷ unique-ls) all-∈ = ⊥-elim (l₁≢l₂ (ℕ.suc-injective (Eq.trans (Eq.sym (variant∈e⇒length-cs n l₁ a cs (All.lookup all-∈ (here Eq.refl)))) (variant∈e⇒length-cs n l₂ a cs (All.lookup all-∈ (there (here Eq.refl)))))))
big n (D 2CC.⟨ l , r ⟩) ls unique-ls all-∈ with partition n D l r ls unique-ls all-∈
big n (D 2CC.⟨ l , r ⟩) ls unique-ls all-∈ | ls₁ , ls₂ , _ , _ , ls₁+ls₂≡ls , unique-ls₁ , ls₁∈l , unique-ls₂ , ls₂∈r =
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

⟦exponential-artifact⟧ : ∀ n c → OC.⟦ exponential-oc n ⟧ₒ c ≡ just (exponential-artifact n)
⟦exponential-artifact⟧ zero c = Eq.refl
⟦exponential-artifact⟧ (suc n) c =
    OC.⟦ exponential-oc (suc n) ⟧ₒ c
  ≡⟨⟩
    OC.⟦ 0 OC.-< exponential-oc n ∷ exponential-oc n ∷ [] >- ⟧ₒ c
  ≡⟨⟩
    just (0 Rose.-< List.catMaybes (List.map (λ x → OC.⟦ x ⟧ₒ c) (exponential-oc n ∷ exponential-oc n ∷ [])) >-)
  ≡⟨⟩
    just (0 Rose.-< List.catMaybes (OC.⟦ exponential-oc n ⟧ₒ c ∷ OC.⟦ exponential-oc n ⟧ₒ c ∷ []) >-)
  ≡⟨ Eq.cong (λ x → just (0 Rose.-< List.catMaybes (x ∷ x ∷ []) >-)) (⟦exponential-artifact⟧ n c) ⟩
    just (0 Rose.-< exponential-artifact n ∷ exponential-artifact n ∷ [] >-)
  ≡⟨⟩
    just (exponential-artifact (suc n))
  ∎
  where
  open Eq.≡-Reasoning

⟦options⟧ : ∀ n l
  → l ≤ n
  → List.catMaybes (List.map (λ e → OC.⟦ e ⟧ₒ (conf l)) (options n))
  ≡ variant-cs l
⟦options⟧ zero .zero z≤n = Eq.refl
⟦options⟧ (suc n) l l≤n with n ℕ.<? l
⟦options⟧ (suc n) l l≤n | no n≮l with n ℕ.<ᵇ l | ℕ.<ᵇ-reflects-< n l
⟦options⟧ (suc n) l l≤n | no n≮l | .false | ofⁿ n≮l' = ⟦options⟧ n l (ℕ.≮⇒≥ n≮l)
⟦options⟧ (suc n) l l≤n | no n≮l | .true | ofʸ n<l = ⊥-elim (n≮l n<l)
⟦options⟧ (suc n) l l≤n | yes n<l = Eq.trans (go (suc n) l n<l) (Eq.cong variant-cs (ℕ.≤∧≮⇒≡ n<l (ℕ.≤⇒≯ l≤n)))
  where
  go : ∀ n l
    → n ≤ l
    → List.catMaybes (List.map (λ e → OC.⟦ e ⟧ₒ (conf l)) (options n))
    ≡ variant-cs n
  go zero l n≤l = Eq.refl
  go (suc n) l n<l with ℕ.<ᵇ-reflects-< n l
  go (suc n) l n<l | reflects-n<l with n <ᵇ l
  go (suc n) l n<l | ofʸ n<l' | .true = Eq.cong (suc n Rose.-< [] >- ∷_) (go n l (ℕ.<⇒≤ n<l))
  go (suc n) l n<l | ofⁿ n≮l | .false = ⊥-elim (n≮l n<l)

⟦oc⟧ : ∀ n l → l ≤ n → OC.⟦ oc n ⟧ (conf l) ≡ variant n l
⟦oc⟧ n l l≤n =
    OC.⟦ oc n ⟧ (conf l)
  ≡⟨⟩
    0 Rose.-< OC.⟦ exponential-oc n ∷ options n ⟧ₒ-recurse (conf l) >-
  ≡⟨⟩
    0 Rose.-< List.catMaybes (List.map (λ e → OC.⟦ e ⟧ₒ (conf l)) (exponential-oc n ∷ options n)) >-
  ≡⟨⟩
    0 Rose.-< List.catMaybes (OC.⟦ exponential-oc n ⟧ₒ (conf l) ∷ List.map (λ e → OC.⟦ e ⟧ₒ (conf l)) (options n)) >-
  ≡⟨ Eq.cong (λ x → 0 Rose.-< List.catMaybes (x ∷ List.map (λ e → OC.⟦ e ⟧ₒ (conf l)) (options n)) >-) (⟦exponential-artifact⟧ n (conf l)) ⟩
    0 Rose.-< List.catMaybes (just (exponential-artifact n) ∷ List.map (λ e → OC.⟦ e ⟧ₒ (conf l)) (options n)) >-
  ≡⟨⟩
    0 Rose.-< exponential-artifact n ∷ List.catMaybes (List.map (λ e → OC.⟦ e ⟧ₒ (conf l)) (options n)) >-
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
⊆⇒All∈ n zero l≤m 2cc oc⊆2cc = []
⊆⇒All∈ n (suc l) (s≤s l≤m) 2cc oc⊆2cc = Eq.subst (All (λ l → variant n l ∈ 2CC.⟦ 2cc ⟧)) (List.applyUpTo-∷ʳ⁺ id l) (All.∷ʳ⁺ (⊆⇒All∈ n l (ℕ.<⇒≤ (s≤s l≤m)) 2cc oc⊆2cc) (Eq.subst (_∈ 2CC.⟦ 2cc ⟧) (⟦oc⟧ n l l≤m) (oc⊆2cc (conf l))))

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
goal n@(suc _) 2cc (oc⊆2cc , 2cc⊆oc) =
  begin-strict
    n * sizeWFOC (oc (4 * n))
  ≡⟨ Eq.cong (n *_) (size-oc (4 * n)) ⟩
    n * (2 ^ (suc (4 * n)) + 2 * (4 * n))
  ≡⟨⟩
    n * (2 * 2 ^ (4 * n) + 2 * (4 * n))
  ≡⟨ Eq.cong (n *_) (ℕ.*-distribˡ-+ 2 (2 ^ (4 * n)) (4 * n)) ⟨
    n * (2 * (2 ^ (4 * n) + 4 * n))
  ≡⟨ ℕ.*-assoc n 2 (2 ^ (4 * n) + 4 * n) ⟨
    n * 2 * (2 ^ (4 * n) + 4 * n)
  <⟨ ℕ.*-monoʳ-< (n * 2) (ℕ.+-monoʳ-< (2 ^ (4 * n)) (4*n<16^n n)) ⟩
    n * 2 * (2 ^ (4 * n) + 16 ^ n)
  ≡⟨ Eq.cong (λ x → n * 2 * (2 ^ (4 * n) + x)) (ℕ.^-*-assoc 2 4 n) ⟩
    n * 2 * (2 ^ (4 * n) + 2 ^ (4 * n))
  ≡⟨ Eq.cong (_* (2 ^ (4 * n) + 2 ^ (4 * n))) (ℕ.*-comm n 2) ⟩
    2 * n * (2 ^ (4 * n) + 2 ^ (4 * n))
  ≡⟨ Eq.cong (λ x → 2 * n * (2 ^ (4 * n) + x)) (ℕ.+-identityʳ (2 ^ (4 * n))) ⟨
    2 * n * (2 ^ (4 * n) + (2 ^ (4 * n) + 0))
  ≡⟨⟩
    2 * n * (2 * 2 ^ (4 * n))
  ≡⟨ ℕ.*-assoc (2 * n) 2 (2 ^ (4 * n)) ⟨
    2 * n * 2 * 2 ^ (4 * n)
  ≡⟨ Eq.cong (_* 2 ^ (4 * n)) (ℕ.*-comm (2 * n) 2) ⟩
    2 * (2 * n) * 2 ^ (4 * n)
  ≡⟨ Eq.cong (_* 2 ^ (4 * n)) (ℕ.*-assoc 2 2 n) ⟨
    (2 * 2) * n * 2 ^ (4 * n)
  ≡⟨⟩
    4 * n * 2 ^ (4 * n)
  ≤⟨ ℕ.*-monoˡ-≤ (2 ^ (4 * n)) (ℕ.m≤n+m (4 * n) 1) ⟩
    suc (4 * n) * 2 ^ (4 * n)
  ≡⟨ Eq.cong (_* 2 ^ (4 * n)) (List.length-upTo (suc (4 * n))) ⟨
    List.length (List.upTo (suc (4 * n))) * 2 ^ (4 * n)
  <⟨ big (4 * n) 2cc (List.upTo (suc (4 * n))) (Unique.applyUpTo⁺₁ id (suc (4 * n)) (λ i<j j<n → ℕ.<⇒≢ i<j)) (⊆⇒All∈ (4 * n) (suc (4 * n)) ℕ.≤-refl 2cc oc⊆2cc) ⟩
    size2CC 2cc
  ∎
  where
  open ℕ.≤-Reasoning

OC≱2CC : SizedWFOC ≱Size Sized2CC
OC≱2CC n = NAT , oc (4 * n) , λ 2cc oc≅2cc → goal n 2cc oc≅2cc
