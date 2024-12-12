module Vatras.SyntacticExpressiveness.2CC<ADT where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Nat as ℕ using (ℕ; suc; zero; _≤_; z≤n; s≤s; _<_; _≮_; _<?_; _+_; pred; _*_; _^_; _≟_)
import Data.Nat.Properties as ℕ
open import Data.Fin as Fin using (Fin; zero; suc)
import Data.Fin.Properties as Fin
open import Data.List as List using (List; []; _∷_)
import Data.List.Properties as List
import Data.List.Membership.Propositional as List
import Data.List.Membership.Propositional.Properties as List
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
import Data.List.NonEmpty.Properties as List⁺
open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (_∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl)
open import Relation.Nullary.Decidable using (Dec; yes; no)
open import Relation.Nullary.Negation using (¬_)
open import Size using (Size; ∞)

open import Vatras.Data.EqIndexedSet using (_≅_; ≅-trans; ≅-sym; _⊆_; ⊆-trans; _∈_)
open import Vatras.Framework.Definitions using (𝔸)
open import Vatras.Framework.Examples using (ℕ-𝔸)
open import Vatras.Framework.Variants using (Rose; Rose-injective)
open import Vatras.Framework.VariantGenerator (Rose ∞) ℕ-𝔸 using (VariantGenerator)
open import Vatras.Framework.Relation.Expression (Rose ∞) using (_,_⊢_≣_)
open import Vatras.Util.List using (find-or-last)
open import Vatras.Lang.All.Fixed ℕ (Rose ∞)
open import Vatras.SyntacticExpressiveness using (_≱Size_; _<Size_)
open import Vatras.SyntacticExpressiveness.Sizes ℕ using (Sized2CC; size2CC; SizedADT; sizeADT)
open import Vatras.SyntacticExpressiveness.2CC≤ADT ℕ using (2CC≤ADT)

e₁-cs : ℕ → ℕ → List (2CC.2CC ∞ ℕ-𝔸)
e₁-cs zero D = []
e₁-cs (suc n) D = D 2CC.2CC.⟨ 0 2CC.2CC.-< [] >- , 1 2CC.2CC.-< [] >- ⟩ ∷ e₁-cs n (suc D)

e₁ : ℕ → 2CC.2CC ∞ ℕ-𝔸
e₁ n = 0 2CC.2CC.-< e₁-cs n zero >-

size-e₁-cs : ∀ n D → List.sum (List.map size2CC (e₁-cs n D)) ≡ n * 3
size-e₁-cs zero D = refl
size-e₁-cs (suc n) D = Eq.cong (3 +_) (size-e₁-cs n (suc D))

size-e₁ : ∀ n → size2CC (e₁ n) ≡ 1 + n * 3
size-e₁ n = Eq.cong suc (size-e₁-cs n zero)

variants-cs : ∀ n → Fin (2 ^ n) → List (Rose ∞ ℕ-𝔸)
variants-cs zero zero = []
variants-cs (suc n) i with Fin.toℕ i <? 2 ^ n
... | yes i<2^n = 0 Rose.-< [] >- ∷ variants-cs n (Fin.fromℕ< i<2^n)
... | no i≮2^n = 1 Rose.-< [] >- ∷ variants-cs n (Eq.subst Fin (ℕ.+-identityʳ (2 ^ n)) (Fin.reduce≥ i (ℕ.≮⇒≥ i≮2^n)))

variants : ∀ n → VariantGenerator (pred (2 ^ n))
variants n i = 0 Rose.-< variants-cs n (Eq.subst Fin (ℕ.suc-pred (2 ^ n) {{ℕ.>-nonZero (ℕ.m^n>0 2 n)}}) i) >-

lemma1 : ∀ n → variants n ⊆ 2CC.⟦ e₁ n ⟧
lemma1 n i = config n i' , Eq.cong (0 Rose.-<_>-) (go n i' zero λ o → Eq.cong (config n i') (ℕ.+-identityʳ o))
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
      (if true then 2CC.⟦ 0 2CC.2CC.-< [] >- ⟧ (config n i') else 2CC.⟦ 1 2CC.2CC.-< [] >- ⟧ (config n i')) ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n i')) (e₁-cs m (suc D))
    ≡⟨ Eq.cong (λ x → (if x then 2CC.⟦ 0 2CC.2CC.-< [] >- ⟧ (config n i') else 2CC.⟦ 1 2CC.2CC.-< [] >- ⟧ (config n i')) ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n i')) (e₁-cs m (suc D))) p' ⟨
      (if config n i' D then 2CC.⟦ 0 2CC.2CC.-< [] >- ⟧ (config n i') else 2CC.⟦ 1 2CC.2CC.-< [] >- ⟧ (config n i')) ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n i')) (e₁-cs m (suc D))
    ≡⟨⟩
      2CC.⟦ D 2CC.2CC.⟨ 0 2CC.2CC.-< [] >- , 1 2CC.2CC.-< [] >- ⟩ ⟧ (config n i') ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n i')) (e₁-cs m (suc D))
    ∎
  ... | no k≮2^m | p' =
    begin
      1 Rose.-< [] >- ∷ variants-cs m j'
    ≡⟨ Eq.cong (1 Rose.-< [] >- ∷_) (go m j' (suc D) (λ o → Eq.trans (Eq.trans (Eq.cong (config n i') (ℕ.+-suc o D)) (p (suc o))) (config-≮2^m m j o k≮2^m))) ⟩
      1 Rose.-< [] >- ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n i')) (e₁-cs m (suc D))
    ≡⟨⟩
      (if false then 2CC.⟦ 0 2CC.2CC.-< [] >- ⟧ (config n i') else 2CC.⟦ 1 2CC.2CC.-< [] >- ⟧ (config n i')) ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n i')) (e₁-cs m (suc D))
    ≡⟨ Eq.cong (λ x → (if x then 2CC.⟦ 0 2CC.2CC.-< [] >- ⟧ (config n i') else 2CC.⟦ 1 2CC.2CC.-< [] >- ⟧ (config n i')) ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n i')) (e₁-cs m (suc D))) p' ⟨
      (if config n i' D then 2CC.⟦ 0 2CC.2CC.-< [] >- ⟧ (config n i') else 2CC.⟦ 1 2CC.2CC.-< [] >- ⟧ (config n i')) ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n i')) (e₁-cs m (suc D))
    ≡⟨⟩
      2CC.⟦ D 2CC.2CC.⟨ 0 2CC.2CC.-< [] >- , 1 2CC.2CC.-< [] >- ⟩ ⟧ (config n i') ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n i')) (e₁-cs m (suc D))
    ∎
    where
    j' = Eq.subst Fin (ℕ.+-identityʳ (2 ^ m)) (Fin.reduce≥ j (ℕ.≮⇒≥ k≮2^m))

ADT-leafs : ADT.ADT ℕ-𝔸 → List⁺ (Rose ∞ ℕ-𝔸)
ADT-leafs (ADT.ADT.leaf v) = v ∷ []
ADT-leafs (D ADT.ADT.⟨ l , r ⟩) = ADT-leafs l List⁺.⁺++⁺ ADT-leafs r

ADT-leaf-count : ADT.ADT ℕ-𝔸 → ℕ
ADT-leaf-count e₂ = List⁺.length (ADT-leafs e₂)

ADT-leaf-count-lemma : ∀ D → (l r : ADT.ADT ℕ-𝔸) → ADT-leaf-count (D ADT.ADT.⟨ l , r ⟩) ≡ ADT-leaf-count l + ADT-leaf-count r
ADT-leaf-count-lemma D l r =
  begin
    ADT-leaf-count (D ADT.ADT.⟨ l , r ⟩)
  ≡⟨⟩
    List⁺.length (ADT-leafs l List⁺.⁺++⁺ ADT-leafs r)
  ≡⟨ Eq.cong List.length (List⁺.toList-⁺++⁺ (ADT-leafs l) (ADT-leafs r)) ⟨
    List.length (List⁺.toList (ADT-leafs l) List.++ List⁺.toList (ADT-leafs r))
  ≡⟨ List.length-++ (List⁺.toList (ADT-leafs l)) ⟩
    ADT-leaf-count l + ADT-leaf-count r
  ∎
  where
  open Eq.≡-Reasoning

leafs-≤-size : (e₂ : ADT.ADT ℕ-𝔸) → ADT-leaf-count e₂ ≤ sizeADT e₂
leafs-≤-size (ADT.ADT.leaf v) = s≤s z≤n
leafs-≤-size (D ADT.ADT.⟨ l , r ⟩) =
  begin
    ADT-leaf-count (D ADT.ADT.⟨ l , r ⟩)
  ≡⟨ ADT-leaf-count-lemma D l r ⟩
    ADT-leaf-count l + ADT-leaf-count r
  ≤⟨ ℕ.+-monoʳ-≤ (ADT-leaf-count l) (leafs-≤-size r) ⟩
    ADT-leaf-count l + sizeADT r
  ≤⟨ ℕ.+-monoˡ-≤ (sizeADT r) (leafs-≤-size l) ⟩
    sizeADT l + sizeADT r
  <⟨ ℕ.n<1+n (sizeADT l + sizeADT r) ⟩
    suc (sizeADT l + sizeADT r)
  ∎
  where
  open ℕ.≤-Reasoning

listToIndexedSet : (vs : List⁺ (Rose ∞ ℕ-𝔸)) → VariantGenerator (pred (List⁺.length vs))
listToIndexedSet vs i = List.lookup (List⁺.toList vs) (Eq.subst Fin (ℕ.suc-pred (List⁺.length vs)) i)

_≟ᵥ_ : ∀ {i} → (v₁ v₂ : Rose i ℕ-𝔸) → Dec (v₁ ≡ v₂)
(a₁ Rose.-< cs₁ >-) ≟ᵥ (a₂ Rose.-< cs₂ >-) with a₁ ℕ.≟ a₂ | List.≡-dec _≟ᵥ_ cs₁ cs₂
(a₁ Rose.-< cs₁ >-) ≟ᵥ (a₂ Rose.-< cs₂ >-) | no a₁≢a₂ | _ = no λ where refl → a₁≢a₂ refl
(a₁ Rose.-< cs₁ >-) ≟ᵥ (a₂ Rose.-< cs₂ >-) | yes a₁≡a₂ | no cs₁≢cs₂ = no (λ where refl → cs₁≢cs₂ refl)
(a₁ Rose.-< cs₁ >-) ≟ᵥ (a₂ Rose.-< cs₂ >-) | yes refl | yes refl = yes refl

ADT-leaf-count≤ₗ : ∀ D l r → ADT-leaf-count l ≤ ADT-leaf-count (D ADT.ADT.⟨ l , r ⟩)
ADT-leaf-count≤ₗ D l r =
  begin
    ADT-leaf-count l
  ≤⟨ ℕ.m≤m+n (ADT-leaf-count l) (ADT-leaf-count r) ⟩
    ADT-leaf-count l + ADT-leaf-count r
  ≡⟨ ADT-leaf-count-lemma D l r ⟨
    ADT-leaf-count (D ADT.ADT.⟨ l , r ⟩)
  ∎
  where
  open ℕ.≤-Reasoning

length-++-≤ₗ : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) → List.length xs ≤ List.length (xs List.++ ys)
length-++-≤ₗ xs ys = Eq.subst (_ ≤_) (Eq.sym (List.length-++ xs)) (ℕ.m≤m+n (List.length xs) (List.length ys))

lookup-++ᵣ : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) i → List.lookup xs i ≡ List.lookup (xs List.++ ys) (Fin.inject≤ i (length-++-≤ₗ xs ys))
lookup-++ᵣ (x ∷ xs) ys zero = refl
lookup-++ᵣ (x ∷ xs) ys (suc i) = lookup-++ᵣ xs ys i

lookup-++ₗ : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) i → List.lookup ys i ≡ List.lookup (xs List.++ ys) (Fin.cast (Eq.sym (List.length-++ xs)) (List.length xs Fin.↑ʳ i))
lookup-++ₗ [] ys i = Eq.cong (List.lookup ys) (Eq.sym (Fin.cast-is-id refl i))
lookup-++ₗ (x ∷ xs) ys i = lookup-++ₗ xs ys i

ADT-leaf∈⟦⟧ : ∀ v e₂ → v ∈ ADT.⟦ e₂ ⟧ → v ∈ listToIndexedSet (ADT-leafs e₂)
ADT-leaf∈⟦⟧ v (ADT.ADT.leaf .v) (c , refl) = zero , refl
ADT-leaf∈⟦⟧ v (D ADT.ADT.⟨ l , r ⟩) (c , p) with c D
ADT-leaf∈⟦⟧ v (D ADT.ADT.⟨ l , r ⟩) (c , p) | true with ADT-leaf∈⟦⟧ v l (c , p)
ADT-leaf∈⟦⟧ v (D ADT.ADT.⟨ l , r ⟩) (c , p) | true | (i , p') = Fin.inject≤ i (ADT-leaf-count≤ₗ D l r) , Eq.trans p' (lookup-++ᵣ (List⁺.toList (ADT-leafs l)) (List⁺.toList (ADT-leafs r)) i)
ADT-leaf∈⟦⟧ v (D ADT.ADT.⟨ l , r ⟩) (c , p) | false with ADT-leaf∈⟦⟧ v r (c , p)
ADT-leaf∈⟦⟧ v (D ADT.ADT.⟨ l , r ⟩) (c , p) | false | (i , p') = (Fin.cast (Eq.sym (ADT-leaf-count-lemma D l r)) (ADT-leaf-count l Fin.↑ʳ i)) , Eq.trans p' (lookup-++ₗ (List⁺.toList (ADT-leafs l)) (List⁺.toList (ADT-leafs r)) i)

ADT-leaf⊆⟦⟧ : ∀ e₂ → ADT.⟦ e₂ ⟧ ⊆ listToIndexedSet (ADT-leafs e₂)
ADT-leaf⊆⟦⟧ e₂ i = ADT-leaf∈⟦⟧ (ADT.⟦ e₂ ⟧ i) e₂ (i , refl)

open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
import Data.List.Relation.Unary.AllPairs.Properties as AllPairs
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
import Data.List.Relation.Binary.Subset.Propositional as List

Unique : ∀ {ℓ} {A : Set ℓ} → List A → Set ℓ
Unique xs = AllPairs _≢_ xs

Fin-reduce≥-injective : ∀ {m n} (i : Fin (m + n)) (j : Fin (m + n)) (m≤i : m ≤ Fin.toℕ i) (m≤j : m ≤ Fin.toℕ j) → Fin.reduce≥ i m≤i ≡ Fin.reduce≥ j m≤j → i ≡ j
Fin-reduce≥-injective {zero} {.(suc _)} zero j m≤i m≤j i≡j = i≡j
Fin-reduce≥-injective {zero} {.(suc _)} (suc i) j m≤i m≤j i≡j = i≡j
Fin-reduce≥-injective {suc m} {zero} (suc i) (suc j) m≤i m≤j i≡j = Eq.cong suc (Fin-reduce≥-injective i j (ℕ.≤-pred m≤i) (ℕ.≤-pred m≤j) i≡j)
Fin-reduce≥-injective {suc m} {suc n} (suc i) (suc j) m≤i m≤j i≡j = Eq.cong suc (Fin-reduce≥-injective i j (ℕ.≤-pred m≤i) (ℕ.≤-pred m≤j) i≡j)

variants-cs-unique : ∀ n i j → i ≢ j → variants-cs n i ≢ variants-cs n j
variants-cs-unique zero zero zero i≢j = ⊥-elim (i≢j refl)
variants-cs-unique (suc n) i j i≢j cs-i≡cs-j with Fin.toℕ i <? 2 ^ n | Fin.toℕ j <? 2 ^ n
... | yes i<2^n | yes j<2^n = variants-cs-unique n (Fin.fromℕ< i<2^n) (Fin.fromℕ< j<2^n) (i≢j ∘ Fin.toℕ-injective ∘ Fin.fromℕ<-injective _ _ i<2^n j<2^n) (proj₂ (List.∷-injective cs-i≡cs-j))
... | yes i<2^n | no j≮2^n = ℕ.0≢1+n (proj₁ (Rose-injective (proj₁ (List.∷-injective cs-i≡cs-j))))
... | no i≮2^n | yes j<2^n = ℕ.0≢1+n (Eq.sym (proj₁ (Rose-injective (proj₁ (List.∷-injective cs-i≡cs-j)))))
... | no i≮2^n | no j≮2^n = variants-cs-unique n (Eq.subst Fin (ℕ.+-identityʳ (2 ^ n)) (Fin.reduce≥ i (ℕ.≮⇒≥ i≮2^n))) (Eq.subst Fin (ℕ.+-identityʳ (2 ^ n)) (Fin.reduce≥ j (ℕ.≮⇒≥ j≮2^n))) (i≢j ∘ Fin-reduce≥-injective i j (ℕ.≮⇒≥ i≮2^n) (ℕ.≮⇒≥ j≮2^n) ∘ Eq.subst-injective (ℕ.+-identityʳ (2 ^ n))) (proj₂ (List.∷-injective cs-i≡cs-j))

variants-unique : ∀ n → Unique (List.tabulate (variants n))
variants-unique n = AllPairs.tabulate⁺ {f = variants n} go
  where
  go : {i j : Fin (suc (pred (2 ^ n)))} → i ≢ j → variants n i ≢ variants n j
  go {i} {j} i≢j vs-i≡vs-j = variants-cs-unique n (Eq.subst Fin (ℕ.suc-pred (2 ^ n) {{ℕ.>-nonZero (ℕ.m^n>0 2 n)}}) i) (Eq.subst Fin (ℕ.suc-pred (2 ^ n) {{ℕ.>-nonZero (ℕ.m^n>0 2 n)}}) j) (i≢j ∘ Eq.subst-injective (ℕ.suc-pred (2 ^ n) {{ℕ.>-nonZero (ℕ.m^n>0 2 n)}})) (proj₂ (Rose-injective vs-i≡vs-j))

IndexedSet-⊆⇒List-⊆ : ∀ {n} (gen : VariantGenerator n) (l : List⁺ (Rose ∞ ℕ-𝔸)) → gen ⊆ listToIndexedSet l → List.tabulate gen List.⊆ List⁺.toList l
IndexedSet-⊆⇒List-⊆ gen l gen⊆l {x} (here refl) with gen⊆l zero
... | i , x∈l = Eq.subst (List._∈ (List⁺.toList l)) (Eq.sym x∈l) (List.∈-lookup {xs = List⁺.toList l} i)
IndexedSet-⊆⇒List-⊆ {suc n} gen l gen⊆l {x} (there x∈gen) = IndexedSet-⊆⇒List-⊆ {n} (gen ∘ suc) l (gen⊆l ∘ suc) x∈gen

lemma5 : ∀ {ℓ} {A : Set ℓ} (u v : A) (xs ys : List A) → u ≢ v → u List.∈ (xs List.++ List.[ v ] List.++ ys) → u List.∈ (xs List.++ ys)
lemma5 u v [] ys u≢v (here u≡v) = ⊥-elim (u≢v u≡v)
lemma5 u v [] ys u≢v (there u∈ys) = u∈ys
lemma5 u v (x ∷ xs) ys u≢v (here u≡x) = here u≡x
lemma5 u v (x ∷ xs) ys u≢v (there u∈xs++v∷ys) = there (lemma5 u v xs ys u≢v u∈xs++v∷ys)

∈∧∉⇒≢ : ∀ {ℓ} {A : Set ℓ} {y z : A} (xs : List A) → y List.∈ xs → All (z ≢_) xs → y ≢ z
∈∧∉⇒≢ (x ∷ xs) (here y≡x) (y≢x ∷ z∉xs) y≡z = y≢x (Eq.trans (Eq.sym y≡z) y≡x)
∈∧∉⇒≢ (x ∷ xs) (there y∈xs) (y≢x ∷ z∉xs) y≡z = ∈∧∉⇒≢ xs y∈xs z∉xs y≡z

length≤ : ∀ {ℓ} {A : Set ℓ} (xs ys : List A) → Unique xs → xs List.⊆ ys → List.length xs ≤ List.length ys
length≤ [] ys unique-xs xs⊆ys = z≤n
length≤ (x ∷ xs) ys unique-xs xs⊆ys with List.∈-∃++ (xs⊆ys (here refl))
length≤ (x ∷ xs) ys (x∉xs ∷ unique-xs) xs⊆ys | l , r , ys≡l++x∷r =
  begin
    List.length (x ∷ xs)
  ≡⟨⟩
    suc (List.length xs)
  ≤⟨ s≤s (length≤ xs (l List.++ r) unique-xs λ {y} y∈xs → lemma5 y x l r (∈∧∉⇒≢ xs y∈xs x∉xs) (Eq.subst (y List.∈_) ys≡l++x∷r (xs⊆ys (there y∈xs)))) ⟩
    suc (List.length (l List.++ r))
  ≡⟨ Eq.cong suc (List.length-++ l) ⟩
    suc (List.length l + List.length r)
  ≡⟨ ℕ.+-suc (List.length l) (List.length r) ⟨
    List.length l + suc (List.length r)
  ≡⟨⟩
    List.length l + List.length (x ∷ r)
  ≡⟨ List.length-++ l ⟨
    List.length (l List.++ (x ∷ r))
  ≡⟨ Eq.cong List.length ys≡l++x∷r ⟨
    List.length ys
  ∎
  where
  open ℕ.≤-Reasoning

lemma3 : ∀ n l → variants n ⊆ listToIndexedSet l → 2 ^ n ≤ List⁺.length l
lemma3 n l variants⊆l =
  begin
    2 ^ n
  ≡⟨ ℕ.suc-pred (2 ^ n) {{ℕ.>-nonZero (ℕ.m^n>0 2 n)}} ⟨
    suc (pred (2 ^ n))
  ≡⟨ List.length-tabulate (variants n) ⟨
    List.length (List.tabulate (variants n))
  ≤⟨ length≤ (List.tabulate (variants n)) (List⁺.toList l) (variants-unique n) (IndexedSet-⊆⇒List-⊆ (variants n) l variants⊆l) ⟩
    List⁺.length l
  ∎
  where
  open ℕ.≤-Reasoning

lemma2 : ∀ n e₂ → variants n ⊆ ADT.⟦ e₂ ⟧ → 2 ^ n ≤ sizeADT e₂
lemma2 n e₂ variants⊆e₂ =
  begin
    2 ^ n
  ≤⟨ lemma3 n (ADT-leafs e₂) (⊆-trans variants⊆e₂ (ADT-leaf⊆⟦⟧ e₂)) ⟩
    ADT-leaf-count e₂
  ≤⟨ leafs-≤-size e₂ ⟩
    sizeADT e₂
  ∎
  where
  open ℕ.≤-Reasoning

lemma4 : ∀ n → 13 * (n * n) < 16 ^ n
lemma4 zero = s≤s z≤n
lemma4 (suc zero) = ℕ.+-monoʳ-≤ 14 z≤n
lemma4 (suc (suc n)) = go (suc n)
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
    <⟨ ℕ.*-monoʳ-< 16 (lemma4 n) ⟩
      16 * 16 ^ n
    ≡⟨⟩
      16 ^ (1 + n)
    ∎

lemma : ∀ n e₂ → 2CC.2CCL , ADT.ADTL ⊢ e₁ (4 * n) ≣ e₂ → n * size2CC (e₁ (4 * n)) < sizeADT e₂
lemma zero (ADT.ADT.leaf v) (e₁⊆e₂ , e₂⊆e₁) = s≤s z≤n
lemma zero (D ADT.ADT.⟨ l , r ⟩) (e₁⊆e₂ , e₂⊆e₁) = s≤s z≤n
lemma (suc m) e₂ (e₁⊆e₂ , e₂⊆e₁) =
  begin-strict
    n * size2CC (e₁ (4 * n))
  ≡⟨ Eq.cong (n *_) (size-e₁ (4 * n)) ⟩
    n * (1 + (4 * n) * 3)
  ≡⟨ ℕ.*-distribˡ-+ n 1 (4 * n * 3) ⟩
    n * 1 + n * (4 * n * 3)
  ≡⟨ Eq.cong (_+ n * (4 * n * 3)) (ℕ.*-identityʳ n) ⟩
    n + n * (4 * n * 3)
  ≡⟨ Eq.cong (λ x → n + n * (x * 3)) (ℕ.*-comm 4 n) ⟩
    n + n * (n * 4 * 3)
  ≡⟨ Eq.cong (λ x → n + n * x) (ℕ.*-assoc n 4 3) ⟩
    n + n * (n * (4 * 3))
  ≡⟨⟩
    n + n * (n * 12)
  ≡⟨ Eq.cong (n +_) (ℕ.*-assoc n n 12) ⟨
    n + n * n * 12
  ≤⟨ ℕ.+-monoˡ-≤ (n * n * 12) (ℕ.m≤m*n n n) ⟩
    n * n + n * n * 12
  ≡⟨ Eq.cong (n * n +_) (ℕ.*-comm (n * n) 12) ⟩
    n * n + 12 * (n * n)
  ≡⟨⟩
    13 * (n * n)
  <⟨ lemma4 n ⟩
    16 ^ n
  ≡⟨ ℕ.^-*-assoc 2 4 n ⟩
    2 ^ (4 * n)
  ≤⟨ lemma2 (4 * n) e₂ (⊆-trans (lemma1 (4 * n)) e₁⊆e₂) ⟩
    sizeADT e₂
  ∎
  where
  open ℕ.≤-Reasoning
  n = suc m

2CC≱ADT : Sized2CC ≱Size SizedADT
2CC≱ADT n = (ℕ , ℕ._≟_) , e₁ (4 * n) , lemma n

2CC<ADT : Sized2CC <Size SizedADT
2CC<ADT = 2CC≤ADT , 2CC≱ADT
