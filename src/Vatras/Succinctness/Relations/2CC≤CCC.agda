open import Vatras.Framework.Definitions using (𝔽; 𝔸; atoms; atomSize)
open import Vatras.Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; _≢_)
open import Data.Nat as ℕ using (ℕ; zero; suc; pred; _≤_; z≤n; s≤s; _<_; _>_; _+_; _∸_; _*_; _<?_; _≤ᵇ_; _^_; _⊔_)
module Vatras.Succinctness.Relations.2CC≤CCC (F : 𝔽) where

open import Data.Bool as Bool using (true; false; if_then_else_)
import Data.Bool.Properties as Bool
open import Data.Empty using (⊥-elim)
import Data.Nat.Properties as ℕ
open import Data.List as List using (List; []; _∷_)
import Data.List.Membership.Propositional.Properties as List
import Data.List.Properties as List
open import Data.List.NonEmpty as List⁺ using (_∷_)
import Data.List.NonEmpty.Properties as List⁺
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)
open import Function using (_∘_; const)
open import Function.Bundles using (Equivalence)
open import Relation.Nullary.Decidable using (yes; no)
open import Size using (Size; ∞)

open import Vatras.Data.EqIndexedSet using (_≅_; _≅[_][_]_; ≅[]-sym; ≅[]→≅; _⊆[_]_)
open import Vatras.Framework.Relation.Function using (to; from)
open import Vatras.Framework.Variants using (Rose)
import Vatras.Util.List as List
open import Vatras.Lang.All
open import Vatras.Framework.Compiler using (LanguageCompiler)
open import Vatras.Succinctness.ProofDefinition using (_≤Size_)
open import Vatras.Succinctness.Sizes using (sizeRose; Sized2CC; size2CC; SizedCCC; sizeCCC; sizeCCC>0)

>⇒¬≤ᵇ : ∀ {m n : ℕ} → m > n → Bool.T (Bool.not (m ≤ᵇ n))
>⇒¬≤ᵇ (s≤s z≤n) = tt
>⇒¬≤ᵇ (s≤s (s≤s m>n)) = >⇒¬≤ᵇ (s≤s m>n)

conf : CCC.Configuration F → 2CC.Configuration (F × ℕ)
conf config (f , n) = config f ≤ᵇ n

fnoc-rec : ℕ → ℕ → 2CC.Configuration (F × ℕ) → CCC.Configuration F
fnoc-rec zero n config f = n
fnoc-rec (suc limit) n config f with config (f , n)
fnoc-rec (suc limit) n config f | true = n
fnoc-rec (suc limit) n config f | false = fnoc-rec limit (suc n) config f

fnoc : ℕ → 2CC.Configuration (F × ℕ) → CCC.Configuration F
fnoc limit config f = fnoc-rec limit zero config f

fnoc-rec-false :
  ∀ (config : 2CC.Configuration (F × ℕ)) (D : F)
  → (limit n k : ℕ)
  → k < fnoc-rec limit n config D
  → (∀ (k' : ℕ) → k' < n → config (D , k') ≡ false)
  → config (D , k) ≡ false
fnoc-rec-false config D zero n k k<fnoc config≡false = config≡false k k<fnoc
fnoc-rec-false config D (suc limit) n k k<fnoc config≡false with config (D , n) in config-n
fnoc-rec-false config D (suc limit) n k k<fnoc config≡false | true = config≡false k k<fnoc
fnoc-rec-false config D (suc limit) n k k<fnoc config≡false | false with n ℕ.≟ k
fnoc-rec-false config D (suc limit) n .n k<fnoc config≡false | false | yes refl = config-n
fnoc-rec-false config D (suc limit) n k k<fnoc config≡false | false | no n≢k' = fnoc-rec-false config D limit (suc n) k k<fnoc lemma
  where
  lemma : ∀ (k' : ℕ) → k' < suc n → config (D , k') ≡ false
  lemma k' k'<n with k' ℕ.≟ n
  lemma k' k'<n | yes refl = config-n
  lemma k' (s≤s k'<n) | no k'≢n = config≡false k' (ℕ.≤∧≢⇒< k'<n k'≢n)

fnoc-rec-true :
  ∀ (config : 2CC.Configuration (F × ℕ))
  → (D : F)
  → (limit n : ℕ)
  → fnoc-rec limit n config D < limit + n
  → config (D , fnoc-rec limit n config D) ≡ true
fnoc-rec-true config D zero n fnoc<limit+n = ⊥-elim (ℕ.n≮n n fnoc<limit+n)
fnoc-rec-true config D (suc limit) n fnoc<limit+n with config (D , n) in config-n
fnoc-rec-true config D (suc limit) n fnoc<limit+n | true = config-n
fnoc-rec-true config D (suc limit) n fnoc<limit+n | false = fnoc-rec-true config D limit (suc n) (ℕ.≤-trans fnoc<limit+n (ℕ.≤-reflexive (Eq.sym (ℕ.+-suc limit n))))

max-dimension : ∀ {i : Size} {A : 𝔸} → CCC.CCC F i A → ℕ
max-dimension (a CCC.CCC.-< cs >-) = List.max (List.map max-dimension cs)
max-dimension (D CCC.CCC.⟨ cs ⟩) = List⁺.length cs ⊔ List.max (List.map max-dimension (List⁺.toList cs))

choice-list : ∀ {A : 𝔸} → F → ℕ → 2CC.2CC (F × ℕ) ∞ A → List (2CC.2CC (F × ℕ) ∞ A) → 2CC.2CC (F × ℕ) ∞ A
choice-list D n c₁ [] = c₁
choice-list D n c₁ (c₂ ∷ []) = (D , n) 2CC.2CC.⟨ c₁ , c₂ ⟩
choice-list D n c₁ (c₂ ∷ c₃ ∷ cs) = (D , n) 2CC.2CC.⟨ c₁ , choice-list D (suc n) c₂ (c₃ ∷ cs) ⟩

choice-list-size :
  ∀ {A : 𝔸} (D : F) (n : ℕ)
  → (c : 2CC.2CC (F × ℕ) ∞ A)
  → (cs : List (2CC.2CC (F × ℕ) ∞ A))
  → size2CC (F × ℕ) (choice-list D n c cs) ≡ List.length cs + List.sum (List.map (size2CC (F × ℕ)) (c ∷ cs))
choice-list-size D n c₁ [] = Eq.sym (ℕ.+-identityʳ (size2CC (F × ℕ) c₁))
choice-list-size D n c₁ (c₂ ∷ []) =
  begin
    size2CC (F × ℕ) (choice-list D n c₁ (c₂ ∷ []))
  ≡⟨⟩
    size2CC (F × ℕ) ((D , n) 2CC.2CC.⟨ c₁ , c₂ ⟩)
  ≡⟨⟩
    suc (size2CC (F × ℕ) c₁ + size2CC (F × ℕ) c₂)
  ≡⟨ Eq.cong (λ x → suc (size2CC (F × ℕ) c₁ + x)) (ℕ.+-identityʳ (size2CC (F × ℕ) c₂)) ⟨
    suc (size2CC (F × ℕ) c₁ + (size2CC (F × ℕ) c₂ + 0))
  ≡⟨⟩
    List.length (c₂ ∷ []) + List.sum (List.map (size2CC (F × ℕ)) (c₁ ∷ c₂ ∷ []))
  ∎
  where
  open Eq.≡-Reasoning
choice-list-size D n c₁ (c₂ ∷ c₃ ∷ cs) =
  begin
    size2CC (F × ℕ) (choice-list D n c₁ (c₂ ∷ c₃ ∷ cs))
  ≡⟨⟩
    size2CC (F × ℕ) ((D , n) 2CC.2CC.⟨ c₁ , choice-list D (suc n) c₂ (c₃ ∷ cs) ⟩)
  ≡⟨⟩
    suc (size2CC (F × ℕ) c₁ + size2CC (F × ℕ) (choice-list D (suc n) c₂ (c₃ ∷ cs)))
  ≡⟨ Eq.cong (λ x → suc (size2CC (F × ℕ) c₁ + x)) (choice-list-size D (suc n) c₂ (c₃ ∷ cs)) ⟩
    suc (size2CC (F × ℕ) c₁ + (List.length (c₃ ∷ cs) + List.sum (List.map (size2CC (F × ℕ)) (c₂ ∷ c₃ ∷ cs))))
  ≡⟨ Eq.cong suc (ℕ.+-assoc (size2CC (F × ℕ) c₁) (List.length (c₃ ∷ cs)) (List.sum (List.map (size2CC (F × ℕ)) (c₂ ∷ c₃ ∷ cs)))) ⟨
    suc (size2CC (F × ℕ) c₁ + List.length (c₃ ∷ cs) + List.sum (List.map (size2CC (F × ℕ)) (c₂ ∷ c₃ ∷ cs)))
  ≡⟨ Eq.cong (λ x → suc (x + List.sum (List.map (size2CC (F × ℕ)) (c₂ ∷ c₃ ∷ cs)))) (ℕ.+-comm (size2CC (F × ℕ) c₁) (List.length (c₃ ∷ cs))) ⟩
    suc (List.length (c₃ ∷ cs) + size2CC (F × ℕ) c₁ + List.sum (List.map (size2CC (F × ℕ)) (c₂ ∷ c₃ ∷ cs)))
  ≡⟨ Eq.cong suc (ℕ.+-assoc (List.length (c₃ ∷ cs)) (size2CC (F × ℕ) c₁) (List.sum (List.map (size2CC (F × ℕ)) (c₂ ∷ c₃ ∷ cs)))) ⟩
    suc (List.length (c₃ ∷ cs) + (size2CC (F × ℕ) c₁ + List.sum (List.map (size2CC (F × ℕ)) (c₂ ∷ c₃ ∷ cs))))
  ≡⟨⟩
    List.length (c₂ ∷ c₃ ∷ cs) + List.sum (List.map (size2CC (F × ℕ)) (c₁ ∷ c₂ ∷ c₃ ∷ cs))
  ∎
  where
  open Eq.≡-Reasoning

translate : ∀ {i : Size} {A : 𝔸}
  → CCC.CCC F i A
  → 2CC.2CC (F × ℕ) ∞ A
translate (a CCC.CCC.-< cs >-) = a 2CC.2CC.-< List.map translate cs >-
translate (D CCC.CCC.⟨ c ∷ cs ⟩) = choice-list D zero (translate c) (List.map translate cs)

translate-size : ∀ {i : Size} {A : 𝔸}
  → (ccc : CCC.CCC F i A)
  → size2CC (F × ℕ) (translate ccc) < 2 * sizeCCC F ccc
translate-size {A = A} (a CCC.CCC.-< cs >-) =
  begin-strict
    size2CC (F × ℕ) (translate (a CCC.CCC.-< cs >-))
  ≡⟨⟩
    size2CC (F × ℕ) (a 2CC.2CC.-< List.map translate cs >-)
  ≡⟨⟩
    suc (atomSize A a + List.sum (List.map (size2CC (F × ℕ)) (List.map translate cs)))
  ≡⟨ Eq.cong (λ x → suc (atomSize A a + List.sum x)) (List.map-∘ cs) ⟨
    suc (atomSize A a + List.sum (List.map (size2CC (F × ℕ) ∘ translate) cs))
  ≤⟨ s≤s (ℕ.+-monoʳ-≤ (atomSize A a) (List.sum-map-≤ (size2CC (F × ℕ) ∘ translate) (λ c → 2 * sizeCCC F c) cs (ℕ.<⇒≤ ∘ translate-size))) ⟩
    suc (atomSize A a + List.sum (List.map (λ c → 2 * sizeCCC F c) cs))
  ≡⟨ Eq.cong (λ x → suc (atomSize A a + List.sum x)) (List.map-∘ cs) ⟩
    suc (atomSize A a + List.sum (List.map (2 *_) (List.map (sizeCCC F) cs)))
  ≡⟨ Eq.cong (λ x → suc (atomSize A a + x)) (List.sum-* 2 (List.map (sizeCCC F) cs)) ⟩
    suc (atomSize A a + 2 * List.sum (List.map (sizeCCC F) cs))
  ≤⟨ s≤s (ℕ.+-monoˡ-≤ (2 * List.sum (List.map (sizeCCC F) cs)) (ℕ.m≤m+n (atomSize A a) (1 * atomSize A a))) ⟩
    suc (atomSize A a + 1 * atomSize A a + 2 * List.sum (List.map (sizeCCC F) cs))
  ≡⟨⟩
    suc (2 * atomSize A a + 2 * List.sum (List.map (sizeCCC F) cs))
  ≡⟨ Eq.cong suc (ℕ.*-distribˡ-+ 2 (atomSize A a) (List.sum (List.map (sizeCCC F) cs))) ⟨
    1 + 2 * (atomSize A a + List.sum (List.map (sizeCCC F) cs))
  <⟨ ℕ.+-monoˡ-< (2 * (atomSize A a + List.sum (List.map (sizeCCC F) cs))) {x = 1} {y = 2} (ℕ.n<1+n 1) ⟩
    2 + 2 * (atomSize A a + List.sum (List.map (sizeCCC F) cs))
  ≡⟨ ℕ.*-suc 2 (atomSize A a + List.sum (List.map (sizeCCC F) cs)) ⟨
    2 * (suc (atomSize A a + List.sum (List.map (sizeCCC F) cs)))
  ≡⟨⟩
    2 * sizeCCC F (a CCC.CCC.-< cs >-)
  ∎
  where
  open ℕ.≤-Reasoning
translate-size (D CCC.CCC.⟨ c ∷ cs ⟩) =
  begin-strict
    size2CC (F × ℕ) (translate (D CCC.CCC.⟨ c ∷ cs ⟩))
  ≡⟨⟩
    size2CC (F × ℕ) (choice-list D zero (translate c) (List.map translate cs))
  ≡⟨ choice-list-size D zero (translate c) (List.map translate cs) ⟩
    List.length (List.map translate cs) + List.sum (List.map (size2CC (F × ℕ)) (List.map translate (c ∷ cs)))
  ≡⟨ Eq.cong (λ x → List.length (List.map translate cs) + List.sum x) (List.map-∘ (c ∷ cs)) ⟨
    List.length (List.map translate cs) + List.sum (List.map (size2CC (F × ℕ) ∘ translate) (c ∷ cs))
  ≤⟨ ℕ.+-monoʳ-≤ (List.length (List.map translate cs)) (List.sum-map-< (size2CC (F × ℕ) ∘ translate) (λ c → 2 * sizeCCC F c) (c ∷ cs) translate-size) ⟩
    List.length (List.map translate cs) + (List.sum (List.map (λ c → 2 * sizeCCC F c) (c ∷ cs)) ∸ List.length (c ∷ cs))
  ≡⟨ Eq.cong (λ x → List.length (List.map translate cs) + (List.sum x ∸ List.length (c ∷ cs))) (List.map-∘ {g = 2 *_} {f = sizeCCC F} (c ∷ cs)) ⟩
    List.length (List.map translate cs) + (List.sum (List.map (2 *_) (List.map (sizeCCC F) (c ∷ cs))) ∸ List.length (c ∷ cs))
  ≡⟨ Eq.cong (λ x → List.length (List.map translate cs) + (x ∸ List.length (c ∷ cs))) (List.sum-* 2 (List.map (sizeCCC F) (c ∷ cs))) ⟩
    List.length (List.map translate cs) + (2 * List.sum (List.map (sizeCCC F) (c ∷ cs)) ∸ List.length (c ∷ cs))
  ≡⟨ Eq.cong (_+ (2 * List.sum (List.map (sizeCCC F) (c ∷ cs)) ∸ List.length (c ∷ cs))) (List.length-map translate cs) ⟩
    List.length cs + (2 * List.sum (List.map (sizeCCC F) (c ∷ cs)) ∸ List.length (c ∷ cs))
  ≡⟨ ℕ.+-∸-assoc (List.length cs) (
    begin
      List.length (c ∷ cs)
    ≡⟨ ℕ.*-identityʳ (List.length (c ∷ cs)) ⟨
      List.length (c ∷ cs) * 1
    ≡⟨ List.sum-replicate (List.length (c ∷ cs)) 1 ⟨
      List.sum (List.replicate (List.length (c ∷ cs)) 1)
    ≡⟨ Eq.cong List.sum (List.map-const 1 (c ∷ cs)) ⟨
      List.sum (List.map (const 1) (c ∷ cs))
    ≤⟨ List.sum-map-≤ (const 1) (sizeCCC F) (c ∷ cs) (sizeCCC>0 F) ⟩
      List.sum (List.map (sizeCCC F) (c ∷ cs))
    ≤⟨ ℕ.m≤n*m (List.sum (List.map (sizeCCC F) (c ∷ cs))) 2 ⟩
      2 * List.sum (List.map (sizeCCC F) (c ∷ cs))
    ∎)
  ⟨
    (List.length cs + 2 * List.sum (List.map (sizeCCC F) (c ∷ cs))) ∸ List.length (c ∷ cs)
  ≤⟨ ℕ.∸-monoʳ-≤ (List.length cs + 2 * List.sum (List.map (sizeCCC F) (c ∷ cs))) (ℕ.n≤1+n (List.length cs)) ⟩
    (List.length cs + 2 * List.sum (List.map (sizeCCC F) (c ∷ cs))) ∸ List.length cs
  ≡⟨ ℕ.m+n∸m≡n (List.length cs) (2 * List.sum (List.map (sizeCCC F) (c ∷ cs))) ⟩
    2 * List.sum (List.map (sizeCCC F) (c ∷ cs))
  <⟨ ℕ.*-monoʳ-< 2 (ℕ.n<1+n (List.sum (List.map (sizeCCC F) (c ∷ cs)))) ⟩
    2 * suc (List.sum (List.map (sizeCCC F) (c ∷ cs)))
  ≡⟨⟩
    2 * sizeCCC F (D CCC.CCC.⟨ c ∷ cs ⟩)
  ∎
  where
  open ℕ.≤-Reasoning

translate-preserves-⊆ : ∀ {i : Size} {A : 𝔸}
  → (e : CCC.CCC F i A)
  → (limit : ℕ)
  → max-dimension e ≤ limit
  → 2CC.⟦ translate e ⟧ ⊆[ fnoc limit ] CCC.⟦ e ⟧
translate-preserves-⊆ e@(a CCC.CCC.-< cs >-) limit max-dim≤limit config =
  begin
    2CC.⟦ translate (a CCC.CCC.-< cs >-) ⟧ config
  ≡⟨⟩
    2CC.⟦ a 2CC.2CC.-< List.map translate cs >- ⟧ config
  ≡⟨⟩
    a Rose.-< List.map (λ c → 2CC.⟦ c ⟧ config) (List.map translate cs) >-
  ≡⟨ Eq.cong (a Rose.-<_>-) (List.map-∘ cs) ⟨
    a Rose.-< List.map (λ c → 2CC.⟦ translate c ⟧ config) cs >-
  ≡⟨ Eq.cong (a Rose.-<_>-) (List.map-cong-with∈ cs (λ c' c'∈cs → translate-preserves-⊆ c' limit (ℕ.≤-trans (List.max-≤ (max-dimension c') (List.map max-dimension cs) (List.∈-map⁺ max-dimension c'∈cs)) max-dim≤limit) config)) ⟩
    a Rose.-< List.map (λ c → CCC.⟦ c ⟧ (fnoc limit config)) cs >-
  ≡⟨⟩
    CCC.⟦ a CCC.CCC.-< cs >- ⟧ (fnoc limit config)
  ∎
  where
  open Eq.≡-Reasoning
translate-preserves-⊆ (D CCC.CCC.⟨ c ∷ cs ⟩) limit max-dim≤limit config =
  begin
    2CC.⟦ translate (D CCC.CCC.⟨ c ∷ cs ⟩) ⟧ config
  ≡⟨⟩
    2CC.⟦ choice-list D zero (translate c) (List.map translate cs) ⟧ config
  ≡⟨ lemma (fnoc limit config D) zero c cs (ℕ.≤-trans (ℕ.m≤m⊔n (List⁺.length (c ∷ cs)) (List.max (List.map max-dimension (c ∷ cs)))) max-dim≤limit) (λ k' k'<fnoc → fnoc-rec-false config D limit zero k' k'<fnoc (λ k' k'<0 → ⊥-elim (ℕ.n≮0 k'<0))) (λ fnoc<limit → fnoc-rec-true config D limit zero (ℕ.≤-trans fnoc<limit (ℕ.≤-reflexive (Eq.sym (ℕ.+-identityʳ limit))))) ⟩
    2CC.⟦ List.find-or-last (fnoc limit config D) (List⁺.map translate (c ∷ cs)) ⟧ config
  ≡⟨ List.map-find-or-last (λ c → 2CC.⟦ c ⟧ config) (fnoc limit config D) (List⁺.map translate (c ∷ cs)) ⟩
    List.find-or-last (fnoc limit config D) (List⁺.map (λ c → 2CC.⟦ c ⟧ config) (List⁺.map translate (c ∷ cs)))
  ≡⟨ Eq.cong (λ x → List.find-or-last (fnoc limit config D) x) (List⁺.map-∘ (c ∷ cs)) ⟨
    List.find-or-last (fnoc limit config D) (List⁺.map (λ c → 2CC.⟦ translate c ⟧ config) (c ∷ cs))
  ≡⟨ Eq.cong (λ x → List.find-or-last (fnoc limit config D) x) (Eq.cong₂ _∷_ (translate-preserves-⊆ c limit (ℕ.≤-trans (ℕ.m≤m⊔n (max-dimension c) (List.max (List.map max-dimension cs))) (ℕ.≤-trans (ℕ.m≤n⊔m (List⁺.length (c ∷ cs)) (List.max (List.map max-dimension (c ∷ cs)))) max-dim≤limit)) config) (List.map-cong-with∈ cs λ c' c'∈cs → translate-preserves-⊆ c' limit (ℕ.≤-trans (List.max-≤ (max-dimension c') (List.map max-dimension cs) (List.∈-map⁺ max-dimension c'∈cs)) (ℕ.≤-trans (ℕ.m≤n⊔m (max-dimension c) (List.max (List.map max-dimension cs))) (ℕ.≤-trans (ℕ.m≤n⊔m (List⁺.length (c ∷ cs)) (List.max (max-dimension c ∷ List.map max-dimension cs))) max-dim≤limit))) config)) ⟩
    List.find-or-last (fnoc limit config D) (CCC.⟦ c ⟧ (fnoc limit config) ∷ List.map (λ c → CCC.⟦ c ⟧ (fnoc limit config)) cs)
  ≡⟨⟩
    List.find-or-last (fnoc limit config D) (List⁺.map (λ c → CCC.⟦ c ⟧ (fnoc limit config)) (c ∷ cs))
  ≡⟨ List.map-find-or-last (λ c → CCC.⟦ c ⟧ (fnoc limit config)) (fnoc limit config D) (c ∷ cs) ⟨
    CCC.⟦ List.find-or-last (fnoc limit config D) (c ∷ cs) ⟧ (fnoc limit config)
  ≡⟨⟩
    CCC.⟦ D CCC.CCC.⟨ c ∷ cs ⟩ ⟧ (fnoc limit config)
  ∎
  where
  open Eq.≡-Reasoning

  lemma : ∀ {i : Size} {A : 𝔸}
    → (m k : ℕ)
    → (c : CCC.CCC F i A)
    → (cs : List (CCC.CCC F i A))
    → k + List.length cs < limit
    → (∀ k' → k' < k + m → config (D , k') ≡ false)
    → (k + m < limit → config (D , k + m) ≡ true)
    → 2CC.⟦ choice-list D k (translate c) (List.map translate cs) ⟧ config ≡ 2CC.⟦ List.find-or-last m (List⁺.map translate (c ∷ cs)) ⟧ config
  lemma zero k c₁ [] k+cs<limit config≡false config≡true = refl
  lemma zero k c₁ (c₂ ∷ []) k+cs<limit config≡false config≡true =
    begin
      2CC.⟦ choice-list D k (translate c₁) (List.map translate (c₂ ∷ [])) ⟧ config
    ≡⟨⟩
      2CC.⟦ (D , k) 2CC.2CC.⟨ translate c₁ , translate c₂ ⟩ ⟧ config
    ≡⟨⟩
      (if config (D , k) then 2CC.⟦ translate c₁ ⟧ config else 2CC.⟦ translate c₂ ⟧ config)
    ≡⟨ Eq.cong (λ x → if x then 2CC.⟦ translate c₁ ⟧ config else 2CC.⟦ translate c₂ ⟧ config) (Eq.subst (λ x → config (D , x) ≡ true) (ℕ.+-identityʳ k) (config≡true (ℕ.≤-<-trans (ℕ.+-monoʳ-≤ k z≤n) k+cs<limit))) ⟩
      (if true then 2CC.⟦ translate c₁ ⟧ config else 2CC.⟦ translate c₂ ⟧ config)
    ≡⟨⟩
      2CC.⟦ translate c₁ ⟧ config
    ≡⟨⟩
      2CC.⟦ List.find-or-last zero (List⁺.map translate (c₁ ∷ c₂ ∷ [])) ⟧ config
    ∎
  lemma zero k c₁ (c₂ ∷ c₃ ∷ cs) k+cs<limit config≡false config≡true =
    begin
      2CC.⟦ choice-list D k (translate c₁) (List.map translate (c₂ ∷ c₃ ∷ cs)) ⟧ config
    ≡⟨⟩
      2CC.⟦ (D , k) 2CC.2CC.⟨ translate c₁ , choice-list D (suc k) (translate c₂) (List.map translate (c₃ ∷ cs)) ⟩ ⟧ config
    ≡⟨⟩
      (if config (D , k) then 2CC.⟦ translate c₁ ⟧ config else 2CC.⟦ choice-list D (suc k) (translate c₂) (List.map translate (c₃ ∷ cs)) ⟧ config)
    ≡⟨ Eq.cong (λ x → if x then 2CC.⟦ translate c₁ ⟧ config else 2CC.⟦ choice-list D (suc k) (translate c₂) (List.map translate (c₃ ∷ cs)) ⟧ config) (Eq.subst (λ x → config (D , x) ≡ true) (ℕ.+-identityʳ k) (config≡true (ℕ.≤-<-trans (ℕ.+-monoʳ-≤ k z≤n) k+cs<limit))) ⟩
      (if true then 2CC.⟦ translate c₁ ⟧ config else 2CC.⟦ choice-list D (suc k) (translate c₂) (List.map translate (c₃ ∷ cs)) ⟧ config)
    ≡⟨⟩
      2CC.⟦ translate c₁ ⟧ config
    ≡⟨⟩
      2CC.⟦ List.find-or-last zero (List⁺.map translate (c₁ ∷ c₂ ∷ c₃ ∷ cs)) ⟧ config
    ∎
  lemma (suc m) k c₁ [] k+cs<limit config≡false config≡true = refl
  lemma (suc m) k c₁ (c₂ ∷ []) k+cs<limit config≡false config≡true =
    begin
      2CC.⟦ choice-list D k (translate c₁) (List.map translate (c₂ ∷ [])) ⟧ config
    ≡⟨⟩
      2CC.⟦ (D , k) 2CC.2CC.⟨ translate c₁ , translate c₂ ⟩ ⟧ config
    ≡⟨⟩
      (if config (D , k) then 2CC.⟦ translate c₁ ⟧ config else 2CC.⟦ translate c₂ ⟧ config)
    ≡⟨ Eq.cong (λ x → if x then 2CC.⟦ translate c₁ ⟧ config else 2CC.⟦ translate c₂ ⟧ config) (config≡false k (ℕ.m<m+n k (s≤s z≤n))) ⟩
      (if false then 2CC.⟦ translate c₁ ⟧ config else 2CC.⟦ translate c₂ ⟧ config)
    ≡⟨⟩
      2CC.⟦ translate c₂ ⟧ config
    ≡⟨⟩
      2CC.⟦ List.find-or-last (suc m) (List⁺.map translate (c₁ ∷ c₂ ∷ [])) ⟧ config
    ∎
  lemma (suc m) k c₁ (c₂ ∷ c₃ ∷ cs) k+cs<limit config≡false config≡true =
    begin
      2CC.⟦ choice-list D k (translate c₁) (List.map translate (c₂ ∷ c₃ ∷ cs)) ⟧ config
    ≡⟨⟩
      2CC.⟦ (D , k) 2CC.2CC.⟨ translate c₁ , choice-list D (suc k) (translate c₂) (List.map translate (c₃ ∷ cs)) ⟩ ⟧ config
    ≡⟨⟩
      (if config (D , k) then 2CC.⟦ translate c₁ ⟧ config else 2CC.⟦ choice-list D (suc k) (translate c₂) (List.map translate (c₃ ∷ cs)) ⟧ config)
    ≡⟨ Eq.cong (λ x → if x then 2CC.⟦ translate c₁ ⟧ config else 2CC.⟦ choice-list D (suc k) (translate c₂) (List.map translate (c₃ ∷ cs)) ⟧ config) (config≡false k (ℕ.m<m+n k (s≤s z≤n))) ⟩
      (if false then 2CC.⟦ translate c₁ ⟧ config else 2CC.⟦ choice-list D (suc k) (translate c₂) (List.map translate (c₃ ∷ cs)) ⟧ config)
    ≡⟨⟩
      2CC.⟦ choice-list D (suc k) (translate c₂) (List.map translate (c₃ ∷ cs)) ⟧ config
    ≡⟨ lemma m (suc k) c₂ (c₃ ∷ cs) (ℕ.≤-trans (s≤s (ℕ.≤-reflexive (Eq.sym (ℕ.+-suc k (List.length (c₃ ∷ cs)))))) k+cs<limit) (λ k' k'<k+m → config≡false k' (Eq.subst (k' <_) (Eq.sym (ℕ.+-suc k m)) k'<k+m)) (λ k+m<limit → Eq.subst (λ x → config (D , x) ≡ true) (ℕ.+-suc k m) (config≡true (ℕ.≤-trans (s≤s (ℕ.≤-reflexive (ℕ.+-suc k m))) k+m<limit))) ⟩
      2CC.⟦ List.find-or-last m (List⁺.map translate (c₂ ∷ c₃ ∷ cs)) ⟧ config
    ≡⟨⟩
      2CC.⟦ List.find-or-last (suc m) (List⁺.map translate (c₁ ∷ c₂ ∷ c₃ ∷ cs)) ⟧ config
    ∎

translate-preserves-⊇ : ∀ {i : Size} {A : 𝔸}
  → (e : CCC.CCC F i A)
  → CCC.⟦ e ⟧ ⊆[ conf ] 2CC.⟦ translate e ⟧
translate-preserves-⊇ (a CCC.CCC.-< cs >-) config =
  begin
    CCC.⟦ a CCC.CCC.-< cs >- ⟧ config
  ≡⟨⟩
    a Rose.-< List.map (λ c → CCC.⟦ c ⟧ config) cs >-
  ≡⟨ Eq.cong (a Rose.-<_>-) (List.map-cong (λ c → translate-preserves-⊇ c config) cs) ⟩
    a Rose.-< List.map (λ c → 2CC.⟦ translate c ⟧ (conf config)) cs >-
  ≡⟨ Eq.cong (a Rose.-<_>-) (List.map-∘ cs) ⟩
    a Rose.-< List.map (λ c → 2CC.⟦ c ⟧ (conf config)) (List.map translate cs) >-
  ≡⟨⟩
    2CC.⟦ a 2CC.2CC.-< List.map translate cs >- ⟧ (conf config)
  ≡⟨⟩
    2CC.⟦ translate (a CCC.CCC.-< cs >-) ⟧ (conf config)
  ∎
  where
  open Eq.≡-Reasoning
translate-preserves-⊇ (D CCC.CCC.⟨ c ∷ cs ⟩) config =
  begin
    CCC.⟦ D CCC.CCC.⟨ c ∷ cs ⟩ ⟧ config
  ≡⟨⟩
    CCC.⟦ List.find-or-last (config D) (c ∷ cs) ⟧ config
  ≡⟨ List.map-find-or-last (λ c → CCC.⟦ c ⟧ config) (config D) (c ∷ cs) ⟩
    List.find-or-last (config D) (List⁺.map (λ c → CCC.⟦ c ⟧ config) (c ∷ cs))
  ≡⟨ Eq.cong (λ x → List.find-or-last (config D) x) (List⁺.map-cong (λ c → translate-preserves-⊇ c config) (c ∷ cs)) ⟩
    List.find-or-last (config D) (List⁺.map (λ c → 2CC.⟦ translate c ⟧ (conf config)) (c ∷ cs))
  ≡⟨ Eq.cong (λ x → List.find-or-last (config D) x) (List⁺.map-∘ (c ∷ cs)) ⟩
    List.find-or-last (config D) (List⁺.map (λ c → 2CC.⟦ c ⟧ (conf config)) (List⁺.map translate (c ∷ cs)))
  ≡⟨ List.map-find-or-last (λ c → 2CC.⟦ c ⟧ (conf config)) (config D) (List⁺.map translate (c ∷ cs)) ⟨
    2CC.⟦ List.find-or-last (config D) (List⁺.map translate (c ∷ cs)) ⟧ (conf config)
  ≡⟨ lemma (config D) zero (Eq.sym (ℕ.+-identityʳ (config D))) c cs ⟩
    2CC.⟦ choice-list D zero (translate c) (List.map translate cs) ⟧ (conf config)
  ≡⟨⟩
    2CC.⟦ translate (D CCC.CCC.⟨ c ∷ cs ⟩) ⟧ (conf config)
  ∎
  where
  open Eq.≡-Reasoning

  lemma : ∀ {i : Size} {A : 𝔸}
    → (m k : ℕ)
    → config D ≡ m + k
    → (c : CCC.CCC F i A)
    → (cs : List (CCC.CCC F i A))
    → 2CC.⟦ List.find-or-last m (List⁺.map translate (c ∷ cs)) ⟧ (conf config) ≡ 2CC.⟦ choice-list D k (translate c) (List.map translate cs) ⟧ (conf config)
  lemma zero k config-D≡m+k c₁ [] = refl
  lemma zero k config-D≡m+k c₁ (c₂ ∷ []) =
    begin
      2CC.⟦ List.find-or-last zero (List⁺.map translate (c₁ ∷ c₂ ∷ [])) ⟧ (conf config)
    ≡⟨⟩
      2CC.⟦ translate c₁ ⟧ (conf config)
    ≡⟨⟩
      (if true then 2CC.⟦ translate c₁ ⟧ (conf config) else 2CC.⟦ translate c₂ ⟧ (conf config))
    ≡⟨ Eq.cong (λ x → if x then 2CC.⟦ translate c₁ ⟧ (conf config) else 2CC.⟦ translate c₂ ⟧ (conf config)) (Equivalence.to Bool.T-≡ (ℕ.≤⇒≤ᵇ (ℕ.≤-refl {k}))) ⟨
      (if zero + k ≤ᵇ k then 2CC.⟦ translate c₁ ⟧ (conf config) else 2CC.⟦ translate c₂ ⟧ (conf config))
    ≡⟨ Eq.cong (λ x → if x ≤ᵇ k then 2CC.⟦ translate c₁ ⟧ (conf config) else 2CC.⟦ translate c₂ ⟧ (conf config)) config-D≡m+k ⟨
      (if config D ≤ᵇ k then 2CC.⟦ translate c₁ ⟧ (conf config) else 2CC.⟦ translate c₂ ⟧ (conf config))
    ≡⟨⟩
      (if conf config (D , k) then 2CC.⟦ translate c₁ ⟧ (conf config) else 2CC.⟦ translate c₂ ⟧ (conf config))
    ≡⟨⟩
      2CC.⟦ (D , k) 2CC.⟨ translate c₁ , translate c₂ ⟩ ⟧ (conf config)
    ≡⟨⟩
      2CC.⟦ choice-list D k (translate c₁) (List.map translate (c₂ ∷ [])) ⟧ (conf config)
    ∎
  lemma zero k config-D≡m+k c₁ (c₂ ∷ c₃ ∷ cs) =
    begin
      2CC.⟦ List.find-or-last zero (List⁺.map translate (c₁ ∷ c₂ ∷ c₃ ∷ cs)) ⟧ (conf config)
    ≡⟨⟩
      2CC.⟦ translate c₁ ⟧ (conf config)
    ≡⟨⟩
      (if true then 2CC.⟦ translate c₁ ⟧ (conf config) else 2CC.⟦ choice-list D (suc k) (translate c₂) (List.map translate (c₃ ∷ cs)) ⟧ (conf config))
    ≡⟨ Eq.cong (λ x → if x then 2CC.⟦ translate c₁ ⟧ (conf config) else 2CC.⟦ choice-list D (suc k) (translate c₂) (List.map translate (c₃ ∷ cs)) ⟧ (conf config)) (Equivalence.to Bool.T-≡ (ℕ.≤⇒≤ᵇ (ℕ.≤-refl {k}))) ⟨
      (if zero + k ≤ᵇ k then 2CC.⟦ translate c₁ ⟧ (conf config) else 2CC.⟦ choice-list D (suc k) (translate c₂) (List.map translate (c₃ ∷ cs)) ⟧ (conf config))
    ≡⟨ Eq.cong (λ x → if x ≤ᵇ k then 2CC.⟦ translate c₁ ⟧ (conf config) else 2CC.⟦ choice-list D (suc k) (translate c₂) (List.map translate (c₃ ∷ cs)) ⟧ (conf config)) config-D≡m+k ⟨
      (if config D ≤ᵇ k then 2CC.⟦ translate c₁ ⟧ (conf config) else 2CC.⟦ choice-list D (suc k) (translate c₂) (List.map translate (c₃ ∷ cs)) ⟧ (conf config))
    ≡⟨⟩
      (if conf config (D , k) then 2CC.⟦ translate c₁ ⟧ (conf config) else 2CC.⟦ choice-list D (suc k) (translate c₂) (List.map translate (c₃ ∷ cs)) ⟧ (conf config))
    ≡⟨⟩
      2CC.⟦ (D , k) 2CC.⟨ translate c₁ , choice-list D (suc k) (translate c₂) (List.map translate (c₃ ∷ cs)) ⟩ ⟧ (conf config)
    ≡⟨⟩
      2CC.⟦ choice-list D k (translate c₁) (List.map translate (c₂ ∷ c₃ ∷ cs)) ⟧ (conf config)
    ∎
  lemma (suc m) k config-D≡m+k c₁ [] = refl
  lemma (suc m) k config-D≡m+k c₁ (c₂ ∷ []) =
    begin
      2CC.⟦ List.find-or-last (suc m) (List⁺.map translate (c₁ ∷ c₂ ∷ [])) ⟧ (conf config)
    ≡⟨⟩
      2CC.⟦ translate c₂ ⟧ (conf config)
    ≡⟨⟩
      (if false then 2CC.⟦ translate c₁ ⟧ (conf config) else 2CC.⟦ translate c₂ ⟧ (conf config))
    ≡⟨ Eq.cong (λ x → if x then 2CC.⟦ translate c₁ ⟧ (conf config) else 2CC.⟦ translate c₂ ⟧ (conf config)) (Equivalence.to Bool.T-not-≡ (>⇒¬≤ᵇ (ℕ.m<n+m k (s≤s z≤n)))) ⟨
      (if (suc m) + k ≤ᵇ k then 2CC.⟦ translate c₁ ⟧ (conf config) else 2CC.⟦ translate c₂ ⟧ (conf config))
    ≡⟨ Eq.cong (λ x → if x ≤ᵇ k then 2CC.⟦ translate c₁ ⟧ (conf config) else 2CC.⟦ translate c₂ ⟧ (conf config)) config-D≡m+k ⟨
      (if config D ≤ᵇ k then 2CC.⟦ translate c₁ ⟧ (conf config) else 2CC.⟦ translate c₂ ⟧ (conf config))
    ≡⟨⟩
      (if conf config (D , k) then 2CC.⟦ translate c₁ ⟧ (conf config) else 2CC.⟦ translate c₂ ⟧ (conf config))
    ≡⟨⟩
      2CC.⟦ (D , k) 2CC.⟨ translate c₁ , translate c₂ ⟩ ⟧ (conf config)
    ≡⟨⟩
      2CC.⟦ choice-list D k (translate c₁) (List.map translate (c₂ ∷ [])) ⟧ (conf config)
    ∎
  lemma (suc m) k config-D≡m+k c₁ (c₂ ∷ c₃ ∷ cs) =
    begin
      2CC.⟦ List.find-or-last (suc m) (List⁺.map translate (c₁ ∷ c₂ ∷ c₃ ∷ cs)) ⟧ (conf config)
    ≡⟨⟩
      2CC.⟦ List.find-or-last m (List⁺.map translate (c₂ ∷ c₃ ∷ cs)) ⟧ (conf config)
    ≡⟨ lemma m (suc k) (Eq.trans config-D≡m+k (Eq.sym (ℕ.+-suc m k))) c₂ (c₃ ∷ cs) ⟩
      2CC.⟦ choice-list D (suc k) (translate c₂) (List.map translate (c₃ ∷ cs)) ⟧ (conf config)
    ≡⟨⟩
      (if false then 2CC.⟦ translate c₁ ⟧ (conf config) else 2CC.⟦ choice-list D (suc k) (translate c₂) (List.map translate (c₃ ∷ cs)) ⟧ (conf config))
    ≡⟨ Eq.cong (λ x → if x then 2CC.⟦ translate c₁ ⟧ (conf config) else 2CC.⟦ choice-list D (suc k) (translate c₂) (List.map translate (c₃ ∷ cs)) ⟧ (conf config)) (Equivalence.to Bool.T-not-≡ (>⇒¬≤ᵇ (ℕ.m<n+m k (s≤s z≤n)))) ⟨
      (if suc m + k ≤ᵇ k then 2CC.⟦ translate c₁ ⟧ (conf config) else 2CC.⟦ choice-list D (suc k) (translate c₂) (List.map translate (c₃ ∷ cs)) ⟧ (conf config))
    ≡⟨ Eq.cong (λ x → if x ≤ᵇ k then 2CC.⟦ translate c₁ ⟧ (conf config) else 2CC.⟦ choice-list D (suc k) (translate c₂) (List.map translate (c₃ ∷ cs)) ⟧ (conf config)) config-D≡m+k ⟨
      (if config D ≤ᵇ k then 2CC.⟦ translate c₁ ⟧ (conf config) else 2CC.⟦ choice-list D (suc k) (translate c₂) (List.map translate (c₃ ∷ cs)) ⟧ (conf config))
    ≡⟨⟩
      (if conf config (D , k) then 2CC.⟦ translate c₁ ⟧ (conf config) else 2CC.⟦ choice-list D (suc k) (translate c₂) (List.map translate (c₃ ∷ cs)) ⟧ (conf config))
    ≡⟨⟩
      2CC.⟦ (D , k) 2CC.⟨ translate c₁ , choice-list D (suc k) (translate c₂) (List.map translate (c₃ ∷ cs)) ⟩ ⟧ (conf config)
    ≡⟨⟩
      2CC.⟦ choice-list D k (translate c₁) (List.map translate (c₂ ∷ c₃ ∷ cs)) ⟧ (conf config)
    ∎

translate-preserves : ∀ {i : Size} {A : 𝔸}
  → (e : CCC.CCC F i A)
  → 2CC.⟦ translate e ⟧ ≅[ fnoc (max-dimension e) ][ conf ] CCC.⟦ e ⟧
translate-preserves e = translate-preserves-⊆ e (max-dimension e) ℕ.≤-refl , translate-preserves-⊇ e

2CC≤CCC : Sized2CC (F × ℕ) ≤Size SizedCCC F
2CC≤CCC = 2 , λ A ccc →
    translate ccc
  , ≅[]→≅ (translate-preserves ccc)
  , ℕ.<⇒≤ (translate-size ccc)

CCC→2CC : LanguageCompiler (CCC.CCCL F) (2CC.2CCL (F × ℕ))
CCC→2CC .LanguageCompiler.compile = translate
CCC→2CC .LanguageCompiler.config-compiler e .to = conf
CCC→2CC .LanguageCompiler.config-compiler e .from = fnoc (max-dimension e)
CCC→2CC .LanguageCompiler.preserves e = ≅[]-sym (translate-preserves e)
