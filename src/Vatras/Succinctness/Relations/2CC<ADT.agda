open import Data.Nat as ℕ using (ℕ; suc; zero; _≤_; z≤n; s≤s; _<_; _≮_; _≤?_; _<?_; _+_; pred; _∸_; _*_; _/_; _^_)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl)
open import Vatras.Framework.Definitions using (𝔽; 𝔸; NAT')

module Vatras.Succinctness.Relations.2CC<ADT
  (F : 𝔽)
  (f : ℕ → F)
  (_==_ : DecidableEquality F)
  (f-injective : ∀ {i j} → i ≢ j → f i ≢ f j)
  where

open import Data.Bool as Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥-elim)
import Data.Nat.Properties as ℕ
import Data.Nat.DivMod as ℕ
open import Data.Fin as Fin using (Fin; zero; suc)
import Data.Fin.Properties as Fin
open import Data.List as List using (List; []; _∷_; _++_)
import Data.List.Properties as List
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_; _⁺++⁺_)
import Data.List.NonEmpty.Properties as List⁺
import Data.List.Membership.Propositional as List
import Data.List.Membership.Propositional.Properties as List
open import Data.List.Relation.Ternary.Interleaving.Propositional using (Interleaving; []; consˡ; consʳ)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
import Data.List.Relation.Unary.Any as Any
import Data.List.Relation.Unary.Any.Properties as Any
import Data.List.Relation.Unary.AllPairs.Properties as AllPairs
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.Propositional.Properties as Unique
open import Data.Product as Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Vec as Vec using (Vec; []; _∷_)
import Data.Vec.Properties as Vec
open import Function using (_∘_; const; id)
open import Relation.Nullary.Decidable using (yes; no)
open import Relation.Unary using (_∈_)
open import Size using (∞)

open import Vatras.Util.AuxProofs using (true≢false)
open import Vatras.Util.Big-O using (𝒪[_])
open import Vatras.Data.EqIndexedSet as IndexedSet using (_⊆_; ⊆-trans)
open import Vatras.Framework.Variants using (Rose; Rose-injective)
open import Vatras.Framework.VariantGenerator (Rose ∞) NAT' using (VariantGenerator)
open import Vatras.Framework.Relation.Expression (Rose ∞) using (_,_⊢_≣_)
open import Vatras.Util.List as List using (find-or-last)
open import Vatras.Translation.Lang.2CC-to-ADT using (ADT≽2CC)
open import Vatras.Succinctness.ProofDefinition (Rose ∞) using (_≰ₛ[_]_; _<ₛ_; ≰ₛ[]-strengthening)
open import Vatras.Succinctness.Sizes using (Sized2CC; size2CC; SizedADT; sizeADT; sizeRose)

open import Vatras.Succinctness.Relations.2CC≤ADT F using (2CC≤ADT)
open import Vatras.Lang.All.Fixed F (Rose ∞)
open 2CC using (2CC; _⟨_,_⟩; _-<_>-; 2CCL)
open ADT using (ADT; _⟨_,_⟩; leaf; ADTL)

e₁-cs : ℕ → ℕ → List (2CC ∞ NAT')
e₁-cs zero D = []
e₁-cs (suc n) D = f D ⟨ 0 -< [] >- , 1 -< [] >- ⟩ ∷ e₁-cs n (suc D)

e₁ : ℕ → 2CC ∞ NAT'
e₁ n = 0 -< e₁-cs n zero >-

size-e₁-cs : ∀ n D → List.sum (List.map size2CC (e₁-cs n D)) ≡ n * 3
size-e₁-cs zero D = refl
size-e₁-cs (suc n) D = Eq.cong (3 +_) (size-e₁-cs n (suc D))

size-e₁ : ∀ n → size2CC (e₁ n) ≡ 1 + n * 3
size-e₁ n = Eq.cong suc (size-e₁-cs n zero)

variants-cs : ∀ n → Vec Bool n → List (Rose ∞ NAT')
variants-cs zero [] = []
variants-cs (suc n) (b ∷ bs) = (if b then 0 else 1) Rose.-< [] >- ∷ variants-cs n bs

variants : ∀ n → Vec Bool n → Rose ∞ NAT'
variants n bs = 0 Rose.-< variants-cs n bs >-

variants-cs-injective : ∀ n bs₁ bs₂ → variants-cs n bs₁ ≡ variants-cs n bs₂ → bs₁ ≡ bs₂
variants-cs-injective zero [] [] refl = refl
variants-cs-injective (suc n) (false ∷ bs₁) (false ∷ bs₂) eq = Eq.cong (false ∷_) (variants-cs-injective n bs₁ bs₂ (List.∷-injectiveʳ eq))
variants-cs-injective (suc n) (true ∷ bs₁) (true ∷ bs₂) eq = Eq.cong (true ∷_) (variants-cs-injective n bs₁ bs₂ (List.∷-injectiveʳ eq))

variants-injective : ∀ n {bs₁} {bs₂} → variants n bs₁ ≡ variants n bs₂ → bs₁ ≡ bs₂
variants-injective n {bs₁} {bs₂} x = variants-cs-injective n bs₁ bs₂ (proj₂ (Rose-injective x))

enumerate-binary : ∀ n → List⁺ (Vec Bool n)
enumerate-binary zero = [] ∷ []
enumerate-binary (suc n) = List⁺.map (true ∷_) (enumerate-binary n) ⁺++⁺ List⁺.map (false ∷_) (enumerate-binary n)

length-enumerate-binary : ∀ n → List⁺.length (enumerate-binary n) ≡ 2 ^ n
length-enumerate-binary zero = refl
length-enumerate-binary (suc n) =
    List⁺.length (enumerate-binary (suc n))
  ≡⟨⟩
    List⁺.length (List⁺.map (true ∷_) (enumerate-binary n) ⁺++⁺ List⁺.map (false ∷_) (enumerate-binary n))
  ≡⟨ List.⁺++⁺-length (List⁺.map (true ∷_) (enumerate-binary n)) (List⁺.map (false ∷_) (enumerate-binary n)) ⟩
    List⁺.length (List⁺.map (true ∷_) (enumerate-binary n)) + List⁺.length (List⁺.map (false ∷_) (enumerate-binary n))
  ≡⟨ Eq.cong₂ _+_ (List⁺.length-map (true ∷_) (enumerate-binary n)) (List⁺.length-map (false ∷_) (enumerate-binary n)) ⟩
    List⁺.length (enumerate-binary n) + List⁺.length (enumerate-binary n)
  ≡⟨ Eq.cong (λ x → x + x) (length-enumerate-binary n) ⟩
    2 ^ n + 2 ^ n
  ≡⟨ Eq.cong (2 ^ n +_) (ℕ.*-identityˡ (2 ^ n)) ⟨
    2 * 2 ^ n
  ≡⟨⟩
    2 ^ suc n
  ∎
  where
  open Eq.≡-Reasoning

enumerate-binary-unique : ∀ n → Unique (List⁺.toList (enumerate-binary n))
enumerate-binary-unique zero = [] ∷ []
enumerate-binary-unique (suc n) = Unique.++⁺
  (Unique.map⁺ Vec.∷-injectiveʳ (enumerate-binary-unique n))
  (Unique.map⁺ Vec.∷-injectiveʳ (enumerate-binary-unique n))
  (λ where (a , b) → true≢false (lemma a) (lemma b))
  where
  lemma : ∀ {v : Vec Bool (suc n)} → {b : Bool} → v List.∈ List.map (b ∷_) (List⁺.toList (enumerate-binary n)) → Vec.head v ≡ b
  lemma {v = b ∷ vs} p = Vec.∷-injectiveˡ (proj₂ (Any.satisfied (Any.map⁻ p)))

simple-drop : ∀ {a} {A : Set a} (n : ℕ) {m : ℕ} → Vec A (n + m) → Vec A m
simple-drop zero xs = xs
simple-drop (suc n) (x ∷ xs) = simple-drop n xs

simple-drop-tail :
  ∀ {a} {A : Set a} {n k : ℕ}
  → (D : ℕ) (xs : Vec A n) (y : A) (zs : Vec A k)
  → (n≡D+m : n ≡ D + suc k)
  → (n≡D+m' : n ≡ suc D + k)
  → simple-drop D (Vec.cast n≡D+m xs) ≡ y ∷ zs
  → simple-drop (suc D) (Vec.cast n≡D+m' xs) ≡ zs
simple-drop-tail zero (x ∷ xs) y zs n≡D+m n≡D+m' h = Vec.∷-injectiveʳ h
simple-drop-tail (suc D) (x ∷ xs) y zs n≡D+m n≡D+m' h = simple-drop-tail D xs y zs (ℕ.suc-injective n≡D+m) (ℕ.suc-injective n≡D+m') h

cast-is-id : ∀ {a} {A : Set a} {n : ℕ} (v : Vec A n) → Vec.cast refl v ≡ v
cast-is-id [] = refl
cast-is-id (x ∷ xs) = Eq.cong (x ∷_) (cast-is-id xs)

variants⊆e₁ : ∀ n → variants n ⊆ 2CC.⟦ e₁ n ⟧
variants⊆e₁ n bs = config n bs , Eq.cong (0 Rose.-<_>-) (go n bs zero refl (cast-is-id bs))
  where
  config' : ∀ (n m : ℕ) → Vec Bool n → 2CC.Configuration
  config' zero m [] d = false
  config' (suc n) m (b ∷ bs) d with f m == d
  config' (suc n) m (b ∷ bs) d | yes f-m≡d = b
  config' (suc n) m (b ∷ bs) d | no f-m≡d = config' n (suc m) bs d

  config : ∀ n → Vec Bool n → 2CC.Configuration
  config n bs d = config' n zero bs d

  config-lemma :
    ∀ m b (bs' : Vec Bool m) D
    → (n≡D+m : n ≡ D + suc m)
    → simple-drop D (Vec.cast n≡D+m bs) ≡ b ∷ bs'
    → config' n zero bs (f D) ≡ b
  config-lemma m b bs' D n≡D+m x = go n zero bs D D b bs' (Eq.sym (ℕ.+-identityʳ D)) n≡D+m x
    where
    go :
      ∀ n m bs D k {x : ℕ} b' (bs' : Vec Bool x)
      → D ≡ k + m
      → (n≡k+x : n ≡ k + suc x)
      → simple-drop k (Vec.cast n≡k+x bs) ≡ b' ∷ bs'
      → config' n m bs (f D) ≡ b'
    go zero m [] D k b' bs' D≡k+m n≡k+x h = ⊥-elim (ℕ.n≮0 (ℕ.≤-trans (ℕ.m≤n+m (suc _) k) (ℕ.≤-reflexive (Eq.sym n≡k+x))))
    go (suc n) m (b ∷ bs) D zero b' bs' D≡k+m n≡k+x h rewrite ℕ.suc-injective n≡k+x rewrite D≡k+m with f m == f m
    go (suc n) m (b ∷ bs) D zero b' bs' D≡k+m n≡k+x h | yes refl = Vec.∷-injectiveˡ h
    go (suc n) m (b ∷ bs) D zero b' bs' D≡k+m n≡k+x h | no f-m≢f-m = ⊥-elim (f-m≢f-m refl)
    go (suc n) m (b ∷ bs) D (suc k) b' bs' D≡k+m n≡k+x h with f m == f D
    go (suc n) m (b ∷ bs) D (suc k) b' bs' D≡k+m n≡k+x h | yes f-m≡f-D = ⊥-elim (f-injective (ℕ.<⇒≢ (ℕ.≤-<-trans (ℕ.m≤n+m m k) (ℕ.<-≤-trans (ℕ.n<1+n (k + m)) (ℕ.≤-reflexive (Eq.sym D≡k+m))))) f-m≡f-D)
    go (suc n) m (b ∷ bs) D (suc k) b' bs' D≡k+m (n≡k+x) h | no f-m≢f-D = go n (suc m) bs D k b' bs' (Eq.trans D≡k+m (Eq.sym (ℕ.+-suc k m))) (ℕ.suc-injective n≡k+x) h

  go : ∀ (m : ℕ) (bs' : Vec Bool m) (D : ℕ) → (n≡D+m : n ≡ D + m) → simple-drop D (Vec.cast n≡D+m bs) ≡ bs'
    → variants-cs m bs' ≡ List.map (λ e → 2CC.⟦ e ⟧ (config n bs)) (e₁-cs m D)
  go zero [] D n≡D+m y = refl
  go (suc m) (true ∷ bs') D n≡D+m y =
      variants-cs (suc m) (true ∷ bs')
    ≡⟨⟩
      0 Rose.-< [] >- ∷ variants-cs m bs'
    ≡⟨ Eq.cong ((0 Rose.-< [] >-) ∷_) (go m bs' (suc D) (Eq.trans n≡D+m (ℕ.+-suc D m)) (simple-drop-tail D bs true bs' n≡D+m (Eq.trans n≡D+m (ℕ.+-suc D m)) y)) ⟩
      0 Rose.-< [] >- ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n bs)) (e₁-cs m (suc D))
    ≡⟨⟩
      (if true then 0 Rose.-< [] >- else 1 Rose.-< [] >-) ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n bs)) (e₁-cs m (suc D))
    ≡⟨ Eq.cong (λ x → (if x then 0 Rose.-< [] >- else 1 Rose.-< [] >-) ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n bs)) (e₁-cs m (suc D))) (config-lemma m true bs' D n≡D+m y) ⟨
      (if config n bs (f D) then 0 Rose.-< [] >- else 1 Rose.-< [] >-) ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n bs)) (e₁-cs m (suc D))
    ≡⟨⟩
      2CC.⟦ f D ⟨ 0 -< [] >- , 1 -< [] >- ⟩ ⟧ (config n bs) ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n bs)) (e₁-cs m (suc D))
    ≡⟨⟩
      List.map (λ e → 2CC.⟦ e ⟧ (config n bs)) (e₁-cs (suc m) D)
    ∎
    where open Eq.≡-Reasoning
  go (suc m) (false ∷ bs') D n≡D+m y =
      variants-cs (suc m) (false ∷ bs')
    ≡⟨⟩
      1 Rose.-< [] >- ∷ variants-cs m bs'
    ≡⟨ Eq.cong ((1 Rose.-< [] >-) ∷_) (go m bs' (suc D) (Eq.trans n≡D+m (ℕ.+-suc D m)) (simple-drop-tail D bs false bs' n≡D+m (Eq.trans n≡D+m (ℕ.+-suc D m)) y)) ⟩
      1 Rose.-< [] >- ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n bs)) (e₁-cs m (suc D))
    ≡⟨⟩
      (if false then 0 Rose.-< [] >- else 1 Rose.-< [] >-) ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n bs)) (e₁-cs m (suc D))
    ≡⟨ Eq.cong (λ x → (if x then 0 Rose.-< [] >- else 1 Rose.-< [] >-) ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n bs)) (e₁-cs m (suc D))) (config-lemma m false bs' D n≡D+m y) ⟨
      (if config n bs (f D) then 0 Rose.-< [] >- else 1 Rose.-< [] >-) ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n bs)) (e₁-cs m (suc D))
    ≡⟨⟩
      2CC.⟦ f D ⟨ 0 -< [] >- , 1 -< [] >- ⟩ ⟧ (config n bs) ∷ List.map (λ e → 2CC.⟦ e ⟧ (config n bs)) (e₁-cs m (suc D))
    ≡⟨⟩
      List.map (λ e → 2CC.⟦ e ⟧ (config n bs)) (e₁-cs (suc m) D)
    ∎
    where open Eq.≡-Reasoning

partition-choice-variants :
  ∀ (D : F)
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

sizeRose-variants-cs : ∀ n bs → List.sum (List.map sizeRose (variants-cs n bs)) ≡ n
sizeRose-variants-cs zero [] = refl
sizeRose-variants-cs (suc n) (b ∷ bs) = Eq.cong suc (sizeRose-variants-cs n bs)

sizeRose-variants : ∀ n bs → sizeRose (variants n bs) ≡ suc n
sizeRose-variants n bs = Eq.cong suc (sizeRose-variants-cs n bs)

sizeRose∈variants :
  ∀ (n : ℕ)
  → (v : Rose ∞ NAT')
  → v List.∈ List.map (variants n) (List⁺.toList (enumerate-binary n))
  → suc n ≡ sizeRose v
sizeRose∈variants n v p with (Any.satisfied (Any.map⁻ p))
sizeRose∈variants n v p | bs , v≡variants-bs =
    suc n
  ≡⟨ sizeRose-variants n bs ⟨
    sizeRose (variants n bs)
  ≡⟨ Eq.cong sizeRose v≡variants-bs ⟨
    sizeRose v
  ∎
  where
  open Eq.≡-Reasoning

lookup≡find-or-last :
  ∀ {a} {A : Set a} (xs : List⁺ A) (i : Fin (List⁺.length xs))
  → List.lookup (List⁺.toList xs) i
  ≡ find-or-last (Fin.toℕ i) xs
lookup≡find-or-last (x ∷ []) zero = refl
lookup≡find-or-last (x₁ ∷ x₂ ∷ xs) zero = refl
lookup≡find-or-last (x₁ ∷ x₂ ∷ xs) (suc i) = lookup≡find-or-last (x₂ ∷ xs) i

lookup-enumerate-binary⊆ :
  ∀ {i} {I : Set i} {a} {A : Set a} {n : ℕ} {M : Vec Bool n → A} {N : I → A}
  → M ⊆ N
  → List.lookup (List.map M (List⁺.toList (enumerate-binary n))) ⊆ N
lookup-enumerate-binary⊆ {n = zero} M⊆N zero = M⊆N []
lookup-enumerate-binary⊆ {I = I} {A = A} {n = suc n} {M = M} {N} M⊆N i with Fin.toℕ i <? List⁺.length (List⁺.map (λ z → M (true ∷ z)) (enumerate-binary n))
lookup-enumerate-binary⊆ {I = I} {A = A} {n = suc n} {M = M} {N} M⊆N i | yes i<2^n = Product.map₂ lemma (lookup-enumerate-binary⊆ (M⊆N ∘ (true ∷_)) (Fin.fromℕ< {Fin.toℕ i} i<2^n))
  where
  open Eq.≡-Reasoning

  lemma : ∀ {j : I}
    → List.lookup (List⁺.toList (List⁺.map (M ∘ (true ∷_)) (enumerate-binary n))) (Fin.fromℕ< i<2^n) ≡ N j
    → List.lookup (List⁺.toList (List⁺.map M (List⁺.map (true ∷_) (enumerate-binary n) ⁺++⁺ List⁺.map (false ∷_) (enumerate-binary n)))) i ≡ N j
  lemma {j} p =
      List.lookup (List⁺.toList (List⁺.map M (List⁺.map (true ∷_) (enumerate-binary n) ⁺++⁺ List⁺.map (false ∷_) (enumerate-binary n)))) i

    ≡⟨ lookup≡find-or-last (List⁺.map M (List⁺.map (true ∷_) (enumerate-binary n) ⁺++⁺ List⁺.map (false ∷_) (enumerate-binary n))) i ⟩
      find-or-last (Fin.toℕ i) (List⁺.map M (List⁺.map (true ∷_) (enumerate-binary n) ⁺++⁺ List⁺.map (false ∷_) (enumerate-binary n)))
    ≡⟨ Eq.cong (λ x → find-or-last (Fin.toℕ i) x) (List.map-⁺++⁺ M (List⁺.map (true ∷_) (enumerate-binary n)) (List⁺.map (false ∷_) (enumerate-binary n))) ⟩
      find-or-last (Fin.toℕ i) (List⁺.map M (List⁺.map (true ∷_) (enumerate-binary n)) ⁺++⁺ List⁺.map M (List⁺.map (false ∷_) (enumerate-binary n)))
    ≡⟨ Eq.cong (λ x → find-or-last (Fin.toℕ i) (x ⁺++⁺ List⁺.map M (List⁺.map (false ∷_) (enumerate-binary n)))) (List⁺.map-∘ (enumerate-binary n)) ⟨
      find-or-last (Fin.toℕ i) (List⁺.map (M ∘ (true ∷_)) (enumerate-binary n) ⁺++⁺ List⁺.map M (List⁺.map (false ∷_) (enumerate-binary n)))
    ≡⟨ List.find-or-last-append (List⁺.map (M ∘ (true ∷_)) (enumerate-binary n)) (List⁺.map M (List⁺.map (false ∷_) (enumerate-binary n))) i<2^n ⟩
      find-or-last (Fin.toℕ i) (List⁺.map (M ∘ (true ∷_)) (enumerate-binary n))
    ≡⟨ Eq.cong (λ x → find-or-last x (List⁺.map (M ∘ (true ∷_)) (enumerate-binary n))) (Fin.toℕ-fromℕ< i<2^n) ⟨
      find-or-last (Fin.toℕ (Fin.fromℕ< i<2^n)) (List⁺.map (M ∘ (true ∷_)) (enumerate-binary n))
    ≡⟨ lookup≡find-or-last (List⁺.map (M ∘ (true ∷_)) (enumerate-binary n)) (Fin.fromℕ< i<2^n) ⟨
      List.lookup (List⁺.toList (List⁺.map (M ∘ (true ∷_)) (enumerate-binary n))) (Fin.fromℕ< i<2^n)
    ≡⟨ p ⟩
      N j
    ∎
lookup-enumerate-binary⊆ {I = I} {A = A} {n = suc n} {M = M} {N} M⊆N i | no i≮2^n = Product.map₂ lemma2 (lookup-enumerate-binary⊆ (M⊆N ∘ (false ∷_)) (Fin.fromℕ< {Fin.toℕ i ∸ 2 ^ n} lemma))
  where
  lemma : Fin.toℕ i ∸ 2 ^ n < List⁺.length (List⁺.map (M ∘ (false ∷_)) (enumerate-binary n))
  lemma =
    begin-strict
      Fin.toℕ i ∸ 2 ^ n
    <⟨ ℕ.∸-monoˡ-< (Fin.toℕ<n i) (ℕ.≤-trans (ℕ.≤-reflexive (Eq.sym (Eq.trans (List⁺.length-map (M ∘ (true ∷_)) (enumerate-binary n)) (length-enumerate-binary n)))) (ℕ.≮⇒≥ i≮2^n)) ⟩
      List⁺.length (List⁺.map M (List⁺.map (true ∷_) (enumerate-binary n) ⁺++⁺ List⁺.map (false ∷_) (enumerate-binary n))) ∸ 2 ^ n
    ≡⟨ Eq.cong (λ x → List⁺.length x ∸ 2 ^ n) (List.map-⁺++⁺ M (List⁺.map (true ∷_) (enumerate-binary n)) (List⁺.map (false ∷_) (enumerate-binary n))) ⟩
      List⁺.length (List⁺.map M (List⁺.map (true ∷_) (enumerate-binary n)) ⁺++⁺ List⁺.map M (List⁺.map (false ∷_) (enumerate-binary n))) ∸ 2 ^ n
    ≡⟨ Eq.cong (_∸ 2 ^ n) (List.⁺++⁺-length (List⁺.map M (List⁺.map (true ∷_) (enumerate-binary n))) (List⁺.map M (List⁺.map (false ∷_) (enumerate-binary n)))) ⟩
      List⁺.length (List⁺.map M (List⁺.map (true ∷_) (enumerate-binary n))) + List⁺.length (List⁺.map M (List⁺.map (false ∷_) (enumerate-binary n))) ∸ 2 ^ n
    ≡⟨ Eq.cong (λ x → List⁺.length x + List⁺.length (List⁺.map M (List⁺.map (false ∷_) (enumerate-binary n))) ∸ 2 ^ n) (List⁺.map-∘ (enumerate-binary n)) ⟨
      List⁺.length (List⁺.map (M ∘ (true ∷_)) (enumerate-binary n)) + List⁺.length (List⁺.map M (List⁺.map (false ∷_) (enumerate-binary n))) ∸ 2 ^ n
    ≡⟨ Eq.cong (λ x → x + List⁺.length (List⁺.map M (List⁺.map (false ∷_) (enumerate-binary n))) ∸ 2 ^ n) (List⁺.length-map (M ∘ (true ∷_)) (enumerate-binary n)) ⟩
      List⁺.length (enumerate-binary n) + List⁺.length (List⁺.map M (List⁺.map (false ∷_) (enumerate-binary n))) ∸ 2 ^ n
    ≡⟨ Eq.cong (λ x → x + List⁺.length (List⁺.map M (List⁺.map (false ∷_) (enumerate-binary n))) ∸ 2 ^ n) (length-enumerate-binary n) ⟩
      2 ^ n + List⁺.length (List⁺.map M (List⁺.map (false ∷_) (enumerate-binary n))) ∸ 2 ^ n
    ≡⟨ Eq.cong (λ x → 2 ^ n + List⁺.length x ∸ 2 ^ n) (List⁺.map-∘ (enumerate-binary n)) ⟨
      2 ^ n + List⁺.length (List⁺.map (M ∘ (false ∷_)) (enumerate-binary n)) ∸ 2 ^ n
    ≡⟨ ℕ.m+n∸m≡n (2 ^ n) (List⁺.length (List⁺.map (M ∘ (false ∷_)) (enumerate-binary n))) ⟩
      List⁺.length (List⁺.map (M ∘ (false ∷_)) (enumerate-binary n))
    ∎
    where
    open ℕ.≤-Reasoning

  open Eq.≡-Reasoning

  lemma2 : ∀ {j : I}
    → List.lookup (List⁺.toList (List⁺.map (M ∘ (false ∷_)) (enumerate-binary n))) (Fin.fromℕ< lemma) ≡ N j
    → List.lookup (List⁺.toList (List⁺.map M (List⁺.map (true ∷_) (enumerate-binary n) ⁺++⁺ List⁺.map (false ∷_) (enumerate-binary n)))) i ≡ N j
  lemma2 {j} p =
      List.lookup (List⁺.toList (List⁺.map M (List⁺.map (true ∷_) (enumerate-binary n) ⁺++⁺ List⁺.map (false ∷_) (enumerate-binary n)))) i
    ≡⟨ lookup≡find-or-last (List⁺.map M (List⁺.map (true ∷_) (enumerate-binary n) ⁺++⁺ List⁺.map (false ∷_) (enumerate-binary n))) i ⟩
      find-or-last (Fin.toℕ i) (List⁺.map M (List⁺.map (true ∷_) (enumerate-binary n) ⁺++⁺ List⁺.map (false ∷_) (enumerate-binary n)))
    ≡⟨ Eq.cong (λ x → find-or-last (Fin.toℕ i) x) (List.map-⁺++⁺ M (List⁺.map (true ∷_) (enumerate-binary n)) (List⁺.map (false ∷_) (enumerate-binary n))) ⟩
      find-or-last (Fin.toℕ i) (List⁺.map M (List⁺.map (true ∷_) (enumerate-binary n)) ⁺++⁺ List⁺.map M (List⁺.map (false ∷_) (enumerate-binary n)))
    ≡⟨ Eq.cong (λ x → find-or-last (Fin.toℕ i) (List⁺.map M (List⁺.map (true ∷_) (enumerate-binary n)) ⁺++⁺ x)) (List⁺.map-∘ (enumerate-binary n)) ⟨
      find-or-last (Fin.toℕ i) (List⁺.map M (List⁺.map (true ∷_) (enumerate-binary n)) ⁺++⁺ List⁺.map (M ∘ (false ∷_)) (enumerate-binary n))
    ≡⟨ List.find-or-last-prepend-∸ (List⁺.map M (List⁺.map (true ∷_) (enumerate-binary n))) (List⁺.map (M ∘ (false ∷_)) (enumerate-binary n)) (ℕ.≤-trans (ℕ.≤-reflexive (Eq.sym (Eq.cong List⁺.length (List⁺.map-∘ (enumerate-binary n))))) (ℕ.≮⇒≥ i≮2^n)) ⟩
      find-or-last (Fin.toℕ i ∸ List⁺.length (List⁺.map M (List⁺.map (true ∷_) (enumerate-binary n)))) (List⁺.map (M ∘ (false ∷_)) (enumerate-binary n))
    ≡⟨ Eq.cong (λ x → find-or-last (Fin.toℕ i ∸ x) (List⁺.map (M ∘ (false ∷_)) (enumerate-binary n))) (List⁺.length-map M (List⁺.map (true ∷_) (enumerate-binary n))) ⟩
      find-or-last (Fin.toℕ i ∸ List⁺.length (List⁺.map (true ∷_) (enumerate-binary n))) (List⁺.map (M ∘ (false ∷_)) (enumerate-binary n))
    ≡⟨ Eq.cong (λ x → find-or-last (Fin.toℕ i ∸ x) (List⁺.map (M ∘ (false ∷_)) (enumerate-binary n))) (List⁺.length-map (true ∷_) (enumerate-binary n)) ⟩
      find-or-last (Fin.toℕ i ∸ List⁺.length (enumerate-binary n)) (List⁺.map (M ∘ (false ∷_)) (enumerate-binary n))
    ≡⟨ Eq.cong (λ x → find-or-last (Fin.toℕ i ∸ x) (List⁺.map (M ∘ (false ∷_)) (enumerate-binary n))) (length-enumerate-binary n) ⟩
      find-or-last (Fin.toℕ i ∸ 2 ^ n) (List⁺.map (M ∘ (false ∷_)) (enumerate-binary n))
    ≡⟨ Eq.cong (λ x → find-or-last x (List⁺.map (M ∘ (false ∷_)) (enumerate-binary n))) (Fin.toℕ-fromℕ< lemma) ⟨
      find-or-last (Fin.toℕ (Fin.fromℕ< lemma)) (List⁺.map (M ∘ (false ∷_)) (enumerate-binary n))
    ≡⟨ lookup≡find-or-last (List⁺.map (M ∘ (false ∷_)) (enumerate-binary n)) (Fin.fromℕ< lemma) ⟨
      List.lookup (List⁺.toList (List⁺.map (M ∘ (false ∷_)) (enumerate-binary n))) (Fin.fromℕ< lemma)
    ≡⟨ p ⟩
      N j
    ∎

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
  ≡⟨ Eq.cong (suc m *_) (length-enumerate-binary m) ⟨
    suc m * List⁺.length (enumerate-binary m)
  ≡⟨ Eq.cong (suc m *_) ((List⁺.length-map (variants m)) (enumerate-binary m)) ⟨
    suc m * List⁺.length (List⁺.map (variants m) (enumerate-binary m))
  ≡⟨ List.sum-map-const (suc m) (List.map (variants m) (List⁺.toList (enumerate-binary m))) ⟨
    List.sum (List.map (const (suc m)) (List.map (variants m) (List⁺.toList (enumerate-binary m))))
  ≡⟨ Eq.cong List.sum (List.map-cong-with∈ (List.map (variants m) (List⁺.toList (enumerate-binary m))) (sizeRose∈variants m)) ⟩
    List.sum (List.map sizeRose (List.map (variants m) (List⁺.toList (enumerate-binary m))))
  ≤⟨ minimal-adt-size e₂ (List.map (variants m) (List⁺.toList (enumerate-binary m))) (Unique.map⁺ (variants-injective m) (enumerate-binary-unique m)) (⊆-trans (lookup-enumerate-binary⊆ (variants⊆e₁ m)) e₁⊆e₂) ⟩
    sizeADT sizeRose e₂
  ∎
  where
  open ℕ.≤-Reasoning
  n = suc k
  m = 3 * n

ADT≰2CC : SizedADT F (Rose ∞) sizeRose ≰ₛ[ (λ n → 2 ^ (n / 3)) ] Sized2CC F
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
    ≡⟨ Eq.cong (32 *_) {n ∸ 15} {suc (n ∸ 16)} (ℕ.+-∸-assoc 1 16≤n) ⟨
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

2CC<ADT : Sized2CC F <ₛ SizedADT F (Rose ∞) sizeRose
2CC<ADT = 2CC≤ADT , ≰ₛ[]-strengthening id∈𝒪[exponential] ADT≰2CC
