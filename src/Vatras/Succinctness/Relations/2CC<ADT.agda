module Vatras.Succinctness.Relations.2CC<ADT where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Nat as ℕ using (ℕ; suc; zero; _≤_; z≤n; s≤s; _<_; _≮_; _≤?_; _<?_; _+_; pred; _∸_; _*_; _/_; _^_)
import Data.Nat.Properties as ℕ
import Data.Nat.DivMod as ℕ
open import Data.Fin as Fin using (Fin; zero; suc)
import Data.Fin.Properties as Fin
open import Data.List as List using (List; []; _∷_)
import Data.List.Properties as List
import Data.List.Membership.Propositional as List
import Data.List.Membership.Propositional.Properties as List
open import Data.List.Relation.Ternary.Interleaving.Propositional using (Interleaving; []; consˡ; consʳ)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
import Data.List.Relation.Unary.AllPairs.Properties as AllPairs
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Function using (_∘_; const; id)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Unary using (_∈_)
open import Size using (∞)

open import Vatras.Util.Big-O using (𝒪[_])
open import Vatras.Data.EqIndexedSet as IndexedSet using (_⊆_; ⊆-trans)
open import Vatras.Framework.Definitions using (𝔸; NAT')
open import Vatras.Framework.Variants using (Rose; Rose-injective)
open import Vatras.Framework.VariantGenerator (Rose ∞) NAT' using (VariantGenerator)
open import Vatras.Framework.Relation.Expression (Rose ∞) using (_,_⊢_≣_)
import Vatras.Util.List as List
open import Vatras.Lang.All.Fixed ℕ (Rose ∞)
open 2CC using (2CC; _⟨_,_⟩; _-<_>-; 2CCL)
open ADT using (ADT; _⟨_,_⟩; leaf; ADTL)
open import Vatras.Translation.Lang.2CC-to-ADT using (ADT≽2CC)
open import Vatras.Succinctness.ProofDefinition (Rose ∞) using (_≰ₛ[_]_; _<ₛ_; ≰ₛ-strengthening)
open import Vatras.Succinctness.Sizes using (Sized2CC; size2CC; SizedADT; sizeADT; sizeRose)
open import Vatras.Succinctness.Relations.2CC≤ADT ℕ using (2CC≤ADT)

e₁-cs : ℕ → ℕ → List (2CC ∞ NAT')
e₁-cs zero D = []
e₁-cs (suc n) D = D ⟨ 0 -< [] >- , 1 -< [] >- ⟩ ∷ e₁-cs n (suc D)

e₁ : ℕ → 2CC ∞ NAT'
e₁ n = 0 -< e₁-cs n zero >-

size-e₁-cs : ∀ n D → List.sum (List.map size2CC (e₁-cs n D)) ≡ n * 3
size-e₁-cs zero D = refl
size-e₁-cs (suc n) D = Eq.cong (3 +_) (size-e₁-cs n (suc D))

size-e₁ : ∀ n → size2CC (e₁ n) ≡ 1 + n * 3
size-e₁ n = Eq.cong suc (size-e₁-cs n zero)

variants-cs : ∀ n → Fin (2 ^ n) → List (Rose ∞ NAT')
variants-cs zero zero = []
variants-cs (suc n) i with Fin.toℕ i <? 2 ^ n
... | yes i<2^n = 0 Rose.-< [] >- ∷ variants-cs n (Fin.fromℕ< i<2^n)
... | no i≮2^n = 1 Rose.-< [] >- ∷ variants-cs n (Eq.subst Fin (ℕ.+-identityʳ (2 ^ n)) (Fin.reduce≥ i (ℕ.≮⇒≥ i≮2^n)))

variants : ∀ n → VariantGenerator (pred (2 ^ n))
variants n i = 0 Rose.-< variants-cs n (Eq.subst Fin (ℕ.suc-pred (2 ^ n) {{ℕ.>-nonZero (ℕ.m^n>0 2 n)}}) i) >-

variants⊆e₁ : ∀ n → variants n ⊆ 2CC.⟦ e₁ n ⟧
variants⊆e₁ n i = config n i' , Eq.cong (0 Rose.-<_>-) (go n i' zero λ o → Eq.cong (config n i') (ℕ.+-identityʳ o))
  where
  i' = Eq.subst Fin (ℕ.suc-pred (2 ^ n) {{ℕ.>-nonZero (ℕ.m^n>0 2 n)}}) i

  config : ∀ n → Fin (2 ^ n) → ℕ → Bool
  config zero zero k = true
  config (suc n) i k with Fin.toℕ i <? 2 ^ n
  config (suc n) i zero | yes i<2^n = true
  config (suc n) i zero | no i≮2^n = false
  config (suc n) i (suc k) | yes i<2^n = config n (Fin.fromℕ< i<2^n) k
  config (suc n) i (suc k) | no i≮2^n = config n (Eq.subst Fin (ℕ.+-identityʳ (2 ^ n)) (Fin.reduce≥ i (ℕ.≮⇒≥ i≮2^n))) k

  open Eq.≡-Reasoning

  config-<2^m : ∀ m j D → (j<2^m : Fin.toℕ j < 2 ^ m) → config (suc m) j (suc D) ≡ config m (Fin.fromℕ< j<2^m) D
  config-<2^m m j D j<2^m with Fin.toℕ j <? 2 ^ m
  ... | yes _ = refl
  ... | no j≮2^m = ⊥-elim (j≮2^m j<2^m)

  config-≮2^m : ∀ m j D → (j≮2^m : Fin.toℕ j ≮ 2 ^ m) → config (suc m) j (suc D) ≡ config m (Eq.subst Fin (ℕ.+-identityʳ (2 ^ m)) (Fin.reduce≥ j (ℕ.≮⇒≥ j≮2^m))) D
  config-≮2^m m j D j≮2^m with Fin.toℕ j <? 2 ^ m
  ... | yes j<2^m = ⊥-elim (j≮2^m j<2^m)
  ... | no _ = refl

  go : ∀ m j D → (∀ o → config n i' (o + D) ≡ config m j o) → variants-cs m j ≡ List.map (λ e → 2CC.⟦ e ⟧ (config n i')) (e₁-cs m D)
  go zero zero D p = refl
  go (suc m) j D p with Fin.toℕ j <? 2 ^ m | p 0
  ... | yes k<2^m | p' =
    begin
      0 Rose.-< [] >- ∷ variants-cs m (Fin.fromℕ< k<2^m)
    ≡⟨ Eq.cong (0 Rose.-< [] >- ∷_) (go m (Fin.fromℕ< k<2^m) (suc D) (λ o → Eq.trans (Eq.trans (Eq.cong (config n i') (ℕ.+-suc o D)) (p (suc o))) (config-<2^m m j o k<2^m))) ⟩
      0 Rose.-< [] >- ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n i')) (e₁-cs m (suc D))
    ≡⟨⟩
      (if true then 2CC.⟦ 0 -< [] >- ⟧ (config n i') else 2CC.⟦ 1 -< [] >- ⟧ (config n i')) ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n i')) (e₁-cs m (suc D))
    ≡⟨ Eq.cong (λ x → (if x then 2CC.⟦ 0 -< [] >- ⟧ (config n i') else 2CC.⟦ 1 -< [] >- ⟧ (config n i')) ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n i')) (e₁-cs m (suc D))) p' ⟨
      (if config n i' D then 2CC.⟦ 0 -< [] >- ⟧ (config n i') else 2CC.⟦ 1 -< [] >- ⟧ (config n i')) ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n i')) (e₁-cs m (suc D))
    ≡⟨⟩
      2CC.⟦ D ⟨ 0 -< [] >- , 1 -< [] >- ⟩ ⟧ (config n i') ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n i')) (e₁-cs m (suc D))
    ∎
  ... | no k≮2^m | p' =
    begin
      1 Rose.-< [] >- ∷ variants-cs m j'
    ≡⟨ Eq.cong (1 Rose.-< [] >- ∷_) (go m j' (suc D) (λ o → Eq.trans (Eq.trans (Eq.cong (config n i') (ℕ.+-suc o D)) (p (suc o))) (config-≮2^m m j o k≮2^m))) ⟩
      1 Rose.-< [] >- ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n i')) (e₁-cs m (suc D))
    ≡⟨⟩
      (if false then 2CC.⟦ 0 -< [] >- ⟧ (config n i') else 2CC.⟦ 1 -< [] >- ⟧ (config n i')) ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n i')) (e₁-cs m (suc D))
    ≡⟨ Eq.cong (λ x → (if x then 2CC.⟦ 0 -< [] >- ⟧ (config n i') else 2CC.⟦ 1 -< [] >- ⟧ (config n i')) ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n i')) (e₁-cs m (suc D))) p' ⟨
      (if config n i' D then 2CC.⟦ 0 -< [] >- ⟧ (config n i') else 2CC.⟦ 1 -< [] >- ⟧ (config n i')) ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n i')) (e₁-cs m (suc D))
    ≡⟨⟩
      2CC.⟦ D ⟨ 0 -< [] >- , 1 -< [] >- ⟩ ⟧ (config n i') ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n i')) (e₁-cs m (suc D))
    ∎
    where
    j' = Eq.subst Fin (ℕ.+-identityʳ (2 ^ m)) (Fin.reduce≥ j (ℕ.≮⇒≥ k≮2^m))

Fin-reduce≥-injective : ∀ {m n} (i : Fin (m + n)) (j : Fin (m + n)) (m≤i : m ≤ Fin.toℕ i) (m≤j : m ≤ Fin.toℕ j) → Fin.reduce≥ i m≤i ≡ Fin.reduce≥ j m≤j → i ≡ j
Fin-reduce≥-injective {zero} {.(suc _)} zero j m≤i m≤j i≡j = i≡j
Fin-reduce≥-injective {zero} {.(suc _)} (suc i) j m≤i m≤j i≡j = i≡j
Fin-reduce≥-injective {suc m} {zero} (suc i) (suc j) m≤i m≤j i≡j = Eq.cong suc (Fin-reduce≥-injective i j (ℕ.≤-pred m≤i) (ℕ.≤-pred m≤j) i≡j)
Fin-reduce≥-injective {suc m} {suc n} (suc i) (suc j) m≤i m≤j i≡j = Eq.cong suc (Fin-reduce≥-injective i j (ℕ.≤-pred m≤i) (ℕ.≤-pred m≤j) i≡j)

variants-cs-unique : ∀ n i j → i ≢ j → variants-cs n i ≢ variants-cs n j
variants-cs-unique zero zero zero i≢j = ⊥-elim (i≢j refl)
variants-cs-unique (suc n) i j i≢j cs-i≡cs-j with Fin.toℕ i <? 2 ^ n | Fin.toℕ j <? 2 ^ n
... | yes i<2^n | yes j<2^n = variants-cs-unique n (Fin.fromℕ< i<2^n) (Fin.fromℕ< j<2^n) (i≢j ∘ Fin.toℕ-injective ∘ Fin.fromℕ<-injective _ _ i<2^n j<2^n) (List.∷-injectiveʳ cs-i≡cs-j)
... | yes i<2^n | no j≮2^n = ℕ.0≢1+n (proj₁ (Rose-injective (List.∷-injectiveˡ cs-i≡cs-j)))
... | no i≮2^n | yes j<2^n = ℕ.0≢1+n (Eq.sym (proj₁ (Rose-injective (List.∷-injectiveˡ cs-i≡cs-j))))
... | no i≮2^n | no j≮2^n = variants-cs-unique n (Eq.subst Fin (ℕ.+-identityʳ (2 ^ n)) (Fin.reduce≥ i (ℕ.≮⇒≥ i≮2^n))) (Eq.subst Fin (ℕ.+-identityʳ (2 ^ n)) (Fin.reduce≥ j (ℕ.≮⇒≥ j≮2^n))) (i≢j ∘ Fin-reduce≥-injective i j (ℕ.≮⇒≥ i≮2^n) (ℕ.≮⇒≥ j≮2^n) ∘ Eq.subst-injective (ℕ.+-identityʳ (2 ^ n))) (List.∷-injectiveʳ cs-i≡cs-j)

variants-unique : ∀ n → Unique (List.tabulate (variants n))
variants-unique n = AllPairs.tabulate⁺ {f = variants n} go
  where
  go : {i j : Fin (suc (pred (2 ^ n)))} → i ≢ j → variants n i ≢ variants n j
  go {i} {j} i≢j vs-i≡vs-j = variants-cs-unique n (Eq.subst Fin (ℕ.suc-pred (2 ^ n) {{ℕ.>-nonZero (ℕ.m^n>0 2 n)}}) i) (Eq.subst Fin (ℕ.suc-pred (2 ^ n) {{ℕ.>-nonZero (ℕ.m^n>0 2 n)}}) j) (i≢j ∘ Eq.subst-injective (ℕ.suc-pred (2 ^ n) {{ℕ.>-nonZero (ℕ.m^n>0 2 n)}})) (proj₂ (Rose-injective vs-i≡vs-j))

partition-choice-variants :
  ∀ (D : ℕ)
  → (l r : ADT NAT')
  → (vs : List (Rose ∞ NAT'))
  → Unique vs
  → List.lookup vs ⊆ ADT.⟦ D ⟨ l , r ⟩ ⟧
  → Σ[ vs₁ ∈ List (Rose ∞ NAT') ]
    Σ[ vs₂ ∈ List (Rose ∞ NAT') ]
      Interleaving vs₁ vs₂ vs
    × Unique vs₁
    × Unique vs₂
    × List.lookup vs₁ ⊆ ADT.⟦ l ⟧
    × List.lookup vs₂ ⊆ ADT.⟦ r ⟧
partition-choice-variants D l r [] unique-vs vs⊆adt = [] , [] , [] , [] , [] , (λ where ()) , (λ where ())
partition-choice-variants D l r (v ∷ vs) (v∉vs ∷ unique-vs) vs⊆adt
  with partition-choice-variants D l r vs unique-vs (vs⊆adt ∘ suc)
... | vs₁ , vs₂ , is-interleaving , unique-vs₁ , unique-vs₂ , vs₁⊆l , vs₂⊆r
  with vs⊆adt zero
... | config , v∈adt
  with config D
... | true = v ∷ vs₁ , vs₂ , consˡ is-interleaving , List.All-Interleavingₗ is-interleaving v∉vs ∷ unique-vs₁ , unique-vs₂ , (λ where
      zero → config , v∈adt
      (suc n) → vs₁⊆l n) , vs₂⊆r
... | false = vs₁ , v ∷ vs₂ , consʳ is-interleaving , unique-vs₁ , List.All-Interleavingᵣ is-interleaving v∉vs ∷ unique-vs₂ , vs₁⊆l , (λ where
      zero → config , v∈adt
      (suc n) → vs₂⊆r n)

minimal-adt-size :
  ∀ (adt : ADT NAT')
  → (vs : List (Rose ∞ NAT'))
  → Unique vs
  → List.lookup vs ⊆ ADT.⟦ adt ⟧
  → List.sum (List.map sizeRose vs) ≤ sizeADT sizeRose adt
minimal-adt-size (leaf v) [] unique-vs vs⊆adt = z≤n
minimal-adt-size (leaf v) (v' ∷ []) unique-vs vs⊆adt with proj₂ (vs⊆adt zero)
minimal-adt-size (leaf v) (v ∷ []) unique-vs vs⊆adt | refl =
  begin
    List.sum (List.map sizeRose (v ∷ []))
  ≡⟨⟩
    sizeRose v + 0
  ≡⟨ ℕ.+-identityʳ (sizeRose v) ⟩
    sizeRose v
  <⟨ ℕ.≤-refl ⟩
    suc (sizeRose v)
  ∎
  where
  open ℕ.≤-Reasoning
minimal-adt-size (leaf v) (v₁ ∷ v₂ ∷ vs) ((v₁≢v₂ ∷ v₁∉vs) ∷ unique-vs) vs⊆adt = ⊥-elim (v₁≢v₂ (Eq.trans (proj₂ (vs⊆adt zero)) (Eq.sym (proj₂ (vs⊆adt (suc zero))))))
minimal-adt-size (D ⟨ l , r ⟩) vs unique-vs vs⊆adt with partition-choice-variants D l r vs unique-vs vs⊆adt
minimal-adt-size (D ⟨ l , r ⟩) vs unique-vs vs⊆adt | vs₁ , vs₂ , is-interleaving , unique-vs₁ , unique-vs₂ , vs₁⊆l , vs₂⊆r =
  begin
    List.sum (List.map sizeRose vs)
  ≡⟨ List.sum-Interleaving (List.map-Interleaving is-interleaving) ⟨
    List.sum (List.map sizeRose vs₁) + List.sum (List.map sizeRose vs₂)
  ≤⟨ ℕ.+-mono-≤ (minimal-adt-size l vs₁ unique-vs₁ vs₁⊆l) (minimal-adt-size r vs₂ unique-vs₂ vs₂⊆r) ⟩
    sizeADT sizeRose l + sizeADT sizeRose r
  <⟨ ℕ.≤-refl ⟩
    suc (sizeADT sizeRose l + sizeADT sizeRose r)
  ≡⟨⟩
    sizeADT sizeRose (D ⟨ l , r ⟩)
  ∎
  where
  open ℕ.≤-Reasoning

13*n^2<16^n : ∀ n → 13 * (n * n) < 16 ^ n
13*n^2<16^n zero = s≤s z≤n
13*n^2<16^n (suc zero) = ℕ.+-monoʳ-≤ 14 z≤n
13*n^2<16^n (suc (suc n)) = go (suc n)
  where
  open ℕ.≤-Reasoning

  go : ∀ n → {{ℕ.NonZero n}} → 13 * ((1 + n) * (1 + n)) < 16 ^ (1 + n)
  go n =
    begin-strict
      13 * ((1 + n) * (1 + n))
    ≤⟨ ℕ.*-monoʳ-≤ 13 (
      begin
        (1 + n) * (1 + n)
      ≡⟨⟩
        1 + n + n * (1 + n)
      ≡⟨ Eq.cong (λ x → 1 + n + x) (ℕ.*-distribˡ-+ n 1 n) ⟩
        1 + n + (n * 1 + n * n)
      ≡⟨ Eq.cong (λ x → 1 + n + (x + n * n)) (ℕ.*-identityʳ n) ⟩
        1 + n + (n + n * n)
      ≡⟨ Eq.cong (λ x → 1 + x) (ℕ.+-assoc n n (n * n)) ⟨
        1 + (n + n + n * n)
      ≤⟨ ℕ.+-monoˡ-≤ (n + n + n * n) (ℕ.m≤n*m 1 n) ⟩
        (n * 1) + (n + n + n * n)
      ≡⟨ Eq.cong (_+ (n + n + n * n)) (ℕ.*-identityʳ n) ⟩
        n + (n + n + n * n)
      ≡⟨ ℕ.+-assoc n (n + n) (n * n) ⟨
        n + (n + n) + n * n
      ≡⟨ Eq.cong (λ x → n + (n + x) + n * n) (ℕ.+-identityʳ n) ⟨
        n + (n + (n + 0)) + n * n
      ≡⟨⟩
        3 * n + n * n
      ≤⟨ ℕ.+-monoˡ-≤ (n * n) (ℕ.*-monoʳ-≤ 3 (ℕ.m≤m*n n n)) ⟩
        3 * (n * n) + n * n
      ≡⟨ ℕ.+-comm (3 * (n * n)) (n * n) ⟩
        n * n + 3 * (n * n)
      ≡⟨⟩
        4 * (n * n)
      ∎
    )⟩
      13 * (4 * (n * n))
    ≤⟨ ℕ.*-monoˡ-≤ (4 * (n * n)) (ℕ.+-monoʳ-≤ 13 (z≤n {3})) ⟩
      16 * (4 * (n * n))
    ≤⟨ ℕ.*-monoʳ-≤ 16 (ℕ.*-monoˡ-≤ (n * n) (ℕ.+-monoʳ-≤ 4 (z≤n {9}))) ⟩
      16 * (13 * (n * n))
    <⟨ ℕ.*-monoʳ-< 16 (13*n^2<16^n n) ⟩
      16 * 16 ^ n
    ≡⟨⟩
      16 ^ (1 + n)
    ∎

sizeRose-variants-cs : ∀ n i → List.sum (List.map sizeRose (variants-cs n i)) ≡ n
sizeRose-variants-cs zero zero = refl
sizeRose-variants-cs (suc n) i with Fin.toℕ i <? 2 ^ n
... | yes i<2^n = Eq.cong suc (sizeRose-variants-cs n (Fin.fromℕ< i<2^n))
... | no i≮2^n = Eq.cong suc (sizeRose-variants-cs n (Eq.subst Fin (ℕ.+-identityʳ (2 ^ n)) (Fin.reduce≥ i (ℕ.≮⇒≥ i≮2^n))))

sizeRose-variants : ∀ n i → sizeRose (variants n i) ≡ suc n
sizeRose-variants n i = Eq.cong suc (sizeRose-variants-cs n (Eq.subst Fin (ℕ.suc-pred (2 ^ n) {{ℕ.>-nonZero (ℕ.m^n>0 2 n)}}) i))

sizeRose∈variants :
  ∀ (n : ℕ)
  → (v : Rose ∞ NAT')
  → v List.∈ List.tabulate (variants n)
  → suc n ≡ sizeRose v
sizeRose∈variants n v v∈vs with List.∈-tabulate⁻ {f = variants n} v∈vs
sizeRose∈variants n v v∈vs | i , refl = Eq.sym (sizeRose-variants n i)

lemma : ∀ n e₂ → ADTL , 2CCL ⊢ e₂ ≣ e₁ (3 * n) → n * 2 ^ (size2CC (e₁ (3 * n)) / 3) < sizeADT sizeRose e₂
lemma zero (leaf v) (e₂⊆e₁ , e₁⊆e₂) = s≤s z≤n
lemma zero (D ⟨ l , r ⟩) (e₂⊆e₁ , e₁⊆e₂) = s≤s z≤n
lemma (suc k) e₂ (e₂⊆e₁ , e₁⊆e₂) =
  begin-strict
    n * 2 ^ (size2CC (e₁ m) / 3)
  ≡⟨ Eq.cong (λ x → n * 2 ^ (x / 3)) (size-e₁ m) ⟩
    n * 2 ^ ((1 + m * 3) / 3)
  ≤⟨ ℕ.*-monoʳ-≤ n (ℕ.^-monoʳ-≤ 2 (ℕ./-monoˡ-≤ 3 (ℕ.+-monoˡ-≤ (m * 3) (s≤s (z≤n {2}))))) ⟩
    n * 2 ^ ((3 + m * 3) / 3)
  ≡⟨ Eq.cong (λ x → n * 2 ^ (x / 3)) (ℕ.*-distribʳ-+ 3 1 m) ⟨
    n * 2 ^ ((1 + m) * 3 / 3)
  ≡⟨ Eq.cong (λ x → n * 2 ^ x) (ℕ.m*n/n≡m (1 + m) 3) ⟩
    n * 2 ^ (1 + m)
  ≡⟨⟩
    n * (2 * 2 ^ m)
  ≡⟨ ℕ.*-assoc n 2 (2 ^ m) ⟨
    n * 2 * 2 ^ m
  <⟨ ℕ.*-monoˡ-< (2 ^ m) {{ℕ.>-nonZero (ℕ.m^n>0 2 m)}} (ℕ.*-monoʳ-< n (ℕ.≤-refl {3})) ⟩
    n * 3 * 2 ^ m
  ≡⟨ Eq.cong (_* 2 ^ m) (ℕ.*-comm n 3) ⟩
    3 * n * 2 ^ m
  ≡⟨⟩
    m * 2 ^ m
  ≤⟨ ℕ.*-monoˡ-≤ (2 ^ m) (ℕ.n≤1+n m) ⟩
    suc m * 2 ^ m
  ≡⟨ Eq.cong (suc m *_) (ℕ.suc-pred (2 ^ m) {{ℕ.>-nonZero (ℕ.m^n>0 2 m)}}) ⟨
    suc m * suc (pred (2 ^ m))
  ≡⟨ Eq.cong (suc m *_) (List.length-tabulate (variants m)) ⟨
    suc m * List.length (List.tabulate (variants m))
  ≡⟨ List.sum-map-const (suc m) (List.tabulate (variants m)) ⟨
    List.sum (List.map (const (suc m)) (List.tabulate (variants m)))
  ≡⟨ Eq.cong List.sum (List.map-cong-with∈ (List.tabulate (variants m)) (sizeRose∈variants m)) ⟩
    List.sum (List.map sizeRose (List.tabulate (variants m)))
  ≤⟨ minimal-adt-size e₂ (List.tabulate (variants m)) (variants-unique m) (⊆-trans (IndexedSet.tabulate⁺ (variants⊆e₁ m)) e₁⊆e₂) ⟩
    sizeADT sizeRose e₂
  ∎
  where
  open ℕ.≤-Reasoning
  n = suc k
  m = 3 * n

ADT≰2CC : SizedADT ℕ (Rose ∞) sizeRose ≰ₛ[ (λ n → 2 ^ (n / 3)) ] Sized2CC ℕ
ADT≰2CC n = NAT' , e₁ (3 * n) , ADT≽2CC (e₁ (3 * n)) , lemma n

2^n≥n : ∀ n → n ≤ 15 * 2 ^ (n / 3)
2^n≥n n with n ≤? 15
2^n≥n n | yes n≤15 =
  begin
    n
  ≤⟨ n≤15 ⟩
    15
  ≤⟨ ℕ.m≤m*n 15 (2 ^ (n / 3)) {{ℕ.>-nonZero (ℕ.m^n>0 2 (n / 3))}} ⟩
    15 * 2 ^ (n / 3)
  ∎
  where
  open ℕ.≤-Reasoning
2^n≥n n | no n≰15 =
  begin
    n
  ≤⟨ All.wfRec <-wellFounded _ (λ n → 16 ≤ n → n ≤ 2 ^ (n / 3)) go n (ℕ.≰⇒> n≰15) ⟩
    2 ^ (n / 3)
  ≤⟨ ℕ.m≤n*m (2 ^ (n / 3)) 15 ⟩
    15 * 2 ^ (n / 3)
  ∎
  where
  open ℕ.≤-Reasoning

  lemma' : ∀ n → 16 ≤ n → 2 ^ 5 * 2 ^ ((n ∸ 15) / 3) ≤ 2 ^ (n / 3)
  lemma' n 16≤n =
    begin
      2 ^ 5 * 2 ^ ((n ∸ 15) / 3)
    ≡⟨ ℕ.^-distribˡ-+-* 2 5 ((n ∸ 15) / 3) ⟨
      2 ^ (5 + (n ∸ 15) / 3)
    ≡⟨ Eq.cong (2 ^_) (ℕ.+-distrib-/ 15 (n ∸ 15) (ℕ.m%n<n (n ∸ 15) 3)) ⟨
      2 ^ ((15 + (n ∸ 15)) / 3)
    ≡⟨ Eq.cong (λ x₁ → 2 ^ (x₁ / 3)) (ℕ.+-∸-assoc 15 (ℕ.≤-trans (ℕ.n≤1+n 15) 16≤n)) ⟨
      2 ^ (((15 + n) ∸ 15) / 3)
    ≡⟨⟩
      2 ^ (n / 3)
    ∎
    where
    open ℕ.≤-Reasoning

  open import Induction.WellFounded
  open import Data.Nat.Induction using (<-Rec; <-wellFounded)

  go :
    ∀ n
    → (∀ {m} → m < n → 16 ≤ m → m ≤ 2 ^ (m / 3))
    → 16 ≤ n
    → n ≤ 2 ^ (n / 3)
  go n rec 16≤n with n ≤? 30
  go n rec 16≤n | yes n≤30 =
    begin
      n
    ≤⟨ ℕ.≤-trans n≤30 (ℕ.m≤m+n 30 2) ⟩
      32
    ≡⟨⟩
      2 ^ 5 * 1
    ≤⟨ ℕ.*-monoʳ-≤ (2 ^ 5) (ℕ.m^n>0 2 ((n ∸ 15) / 3)) ⟩
      2 ^ 5 * 2 ^ ((n ∸ 15) / 3)
    ≤⟨ lemma' n 16≤n ⟩
      2 ^ (n / 3)
    ∎
    where
    open ℕ.≤-Reasoning
  go n rec 16≤n | no n≰30 =
    begin
      n
    ≤⟨ ℕ.m≤n+m n 16 ⟩
      16 + n
    ≡⟨⟩
      32 + n ∸ 16
    ≡⟨ ℕ.+-∸-assoc 32 16≤n ⟩
      32 + (n ∸ 16)
    ≤⟨ ℕ.+-monoʳ-≤ 32 (ℕ.m≤n*m (n ∸ 16) 32) ⟩
      32 + 32 * (n ∸ 16)
    ≡⟨ ℕ.*-suc 32 (n ∸ 16) ⟨
      32 * suc (n ∸ 16)
    ≡⟨ Eq.cong (32 *_) (ℕ.+-∸-assoc 1 16≤n) ⟨
      32 * (n ∸ 15)
    ≡⟨⟩
      2 ^ 5 * (n ∸ 15)
    ≤⟨ ℕ.*-monoʳ-≤ (2 ^ 5) (rec {n ∸ 15} (
      begin-strict
        n ∸ 15
      <⟨ ℕ.∸-monoʳ-< {n} {15} {0} (s≤s (z≤n {14})) (ℕ.≤-trans (ℕ.n≤1+n 15) 16≤n) ⟩
        n
      ∎) (ℕ.∸-monoˡ-≤ 15 (ℕ.≰⇒> n≰30)))
    ⟩
      2 ^ 5 * 2 ^ ((n ∸ 15) / 3)
    ≤⟨ lemma' n 16≤n ⟩
      2 ^ (n / 3)
    ∎
    where
    open ℕ.≤-Reasoning

id∈𝒪[exponential] : id ∈ 𝒪[ (λ n → 2 ^ (n / 3)) ]
id∈𝒪[exponential] .proj₁ = 15
id∈𝒪[exponential] .proj₂ n = 2^n≥n n

2CC<ADT : Sized2CC ℕ <ₛ SizedADT ℕ (Rose ∞) sizeRose
2CC<ADT = 2CC≤ADT , ≰ₛ-strengthening id∈𝒪[exponential] ADT≰2CC
