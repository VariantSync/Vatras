open import Data.Nat using (ℕ; zero; suc; _+_; _*_; pred; _∸_; _≟_; _≤_; _<_; z≤n; s≤s; _<?_; _≤?_; _⊔_)
open import Vatras.Framework.Definitions using (𝔽; 𝔸; 𝕍)

module Vatras.Succinctness.Relations.ADT≤NADT (F : 𝔽) (V : 𝕍) (sizeV : ∀ {A : 𝔸} → V A → ℕ) where

open import Data.Bool using (true; false; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; length; map; sum)
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.Nat.Properties as ℕ
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Relation.Nullary.Decidable using (does; yes; no)
open import Size using (Size; ∞; ↑_)

open import Vatras.Util.List as List using (find-or-last; max)
open import Vatras.Data.EqIndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]→≅)
open import Vatras.Succinctness.ProofDefinition V using (_≤ₛ_)
open import Vatras.Succinctness.Sizes using (SizedNADT; sizeNADT; sizeNADT>0; SizedADT; sizeADT)
open import Vatras.Lang.All
open ADT using (ADT)
open NADT using (NADT)

open import Vatras.Translation.Lang.ADT-to-VariantList using ()

translate : ∀ {i : Size} {A : 𝔸} → NADT F V i A → ADT (F × ℕ) V A
translate-cs : ∀ {i : Size} {A : 𝔸} → F → ℕ → (NADT F V i A) → List (NADT F V i A) → ADT (F × ℕ) V A

-- TODO why do I need ADT.ADT
translate (NADT.leaf v) = ADT.ADT.leaf v
translate (f NADT.⟨ c ∷ cs ⟩) = translate-cs f zero c cs

translate-cs f n c [] = translate c
translate-cs f n c₁ (c₂ ∷ cs) = (f , n) ADT.ADT.⟨ translate c₁ , translate-cs f (suc n) c₂ cs ⟩

⌈_⌉ : ∀ {i : Size} {A : 𝔸} → NADT F V i A → ℕ
⌈ NADT.leaf v ⌉ = 1
⌈ f NADT.⟨ c ∷ cs ⟩ ⌉ = length (c ∷ cs) ⊔ max (map ⌈_⌉ (c ∷ cs))

data ChoiceArity≤ (n : ℕ) {A : 𝔸} : {i : Size} → NADT F V i A → Set₁ where
  leaf :
    ∀ {i : Size}
    → (v : V A)
    → ChoiceArity≤ n {i = ↑ i} (NADT.NADT.leaf v)
  choice :
    ∀ {i : Size}
    → (f : F)
    → (c : NADT F V i A)
    → (cs : List (NADT F V i A))
    → length (c ∷ cs) ≤ n
    → All (ChoiceArity≤ n) (c ∷ cs)
    → ChoiceArity≤ n (f NADT.NADT.⟨ c ∷ cs ⟩)

⌈⌉-head :
  ∀ {i : Size} {A : 𝔸}
  → (c : NADT F V i A)
  → (cs : List (NADT F V i A))
  → ⌈ c ⌉ ≤ length (c ∷ cs) ⊔ max (map ⌈_⌉ (c ∷ cs))
⌈⌉-head c cs =
  begin
    ⌈ c ⌉
  ≤⟨ ℕ.m≤m⊔n ⌈ c ⌉ (max (map ⌈_⌉ cs)) ⟩
    ⌈ c ⌉ ⊔ max (map ⌈_⌉ cs)
  ≤⟨ ℕ.m≤n⊔m (length (c ∷ cs)) (⌈ c ⌉ ⊔ max (map ⌈_⌉ cs)) ⟩
    length (c ∷ cs) ⊔ (⌈ c ⌉ ⊔ max (map ⌈_⌉ cs))
  ≡⟨⟩
    length (c ∷ cs) ⊔ max (map ⌈_⌉ (c ∷ cs))
  ∎
  where
  open ℕ.≤-Reasoning

⌈⌉-tail :
  ∀ {i : Size} {A : 𝔸}
  → (c : NADT F V i A)
  → (cs : List (NADT F V i A))
  → length cs ⊔ max (map ⌈_⌉ cs) ≤ length (c ∷ cs) ⊔ max (map ⌈_⌉ (c ∷ cs))
⌈⌉-tail c cs =
  begin
    length cs ⊔ max (map ⌈_⌉ cs)
  ≤⟨ ℕ.⊔-monoʳ-≤ (length cs) (ℕ.m≤n⊔m ⌈ c ⌉ (max (map ⌈_⌉ cs))) ⟩
    length cs ⊔ (⌈ c ⌉ ⊔ max (map ⌈_⌉ cs))
  ≤⟨ ℕ.⊔-monoˡ-≤ (⌈ c ⌉ ⊔ max (map ⌈_⌉ cs)) (ℕ.n≤1+n (length cs)) ⟩
    length (c ∷ cs) ⊔ (⌈ c ⌉ ⊔ max (map ⌈_⌉ cs))
  ≡⟨⟩
    length (c ∷ cs) ⊔ max (map ⌈_⌉ (c ∷ cs))
  ∎
  where
  open ℕ.≤-Reasoning

weaken-ChoiceArity :
  ∀ {i : Size} → {A : 𝔸}
  → {m n : ℕ}
  → m ≤ n
  → {nadt : NADT F V i A}
  → ChoiceArity≤ m nadt
  → ChoiceArity≤ n nadt
weaken-ChoiceArity m≤n (leaf v) = leaf v
weaken-ChoiceArity m≤n (choice f c cs cs≤m ChoiceArity-cs) = choice f c cs (ℕ.≤-trans cs≤m m≤n) (All.map (weaken-ChoiceArity m≤n) ChoiceArity-cs)

ChoiceArity≤-⌈⌉ : ∀ {i : Size} → {A : 𝔸} → (nadt : NADT F V i A) → ChoiceArity≤ ⌈ nadt ⌉ nadt
ChoiceArity≤-⌈⌉ (NADT.leaf v) = leaf v
ChoiceArity≤-⌈⌉ {A = A} (f NADT.⟨ c ∷ cs ⟩) = choice f c cs (ℕ.m≤m⊔n (length (c ∷ cs)) (max (map ⌈_⌉ (c ∷ cs)))) (lemma c cs)
  where
  open ℕ.≤-Reasoning

  lemma : ∀ {i : Size} → (c : NADT F V i A) → (cs : List (NADT F V i A)) → All (ChoiceArity≤ ⌈ f NADT.NADT.⟨ c ∷ cs ⟩ ⌉) (c ∷ cs)
  lemma c [] = weaken-ChoiceArity (⌈⌉-head c []) (ChoiceArity≤-⌈⌉ c) ∷ []
  lemma c₁ (c₂ ∷ cs) =
      weaken-ChoiceArity (⌈⌉-head c₁ (c₂ ∷ cs)) (ChoiceArity≤-⌈⌉ c₁)
    ∷ All.map (weaken-ChoiceArity (⌈⌉-tail c₁ (c₂ ∷ cs))) (lemma c₂ cs)

conf' : ℕ → ℕ → ADT.Configuration (F × ℕ) → NADT.Configuration F
conf' zero n config f = n
conf' (suc fuel) n config f with config (f , n)
conf' (suc fuel) n config f | true = n
conf' (suc fuel) n config f | false = conf' fuel (suc n) config f

conf : ℕ → ADT.Configuration (F × ℕ) → NADT.Configuration F
conf fuel config f = conf' fuel zero config f

fnoc : NADT.Configuration F → ADT.Configuration (F × ℕ)
fnoc config (f , n) = does (config f ≤? n)

conf≡n :
  ∀ fuel n config f goal
  → goal < n + fuel
  → n ≤ goal
  → (∀ k → k < goal → config (f , k) ≡ false)
  → config (f , goal) ≡ true
  → conf' fuel n config f ≡ goal
conf≡n zero n config f goal goal<n+fuel n≤goal config≡false config≡true
  = ⊥-elim (ℕ.≤⇒≯ n≤goal (proj₁ ℕ.<-resp₂-≡ (ℕ.+-identityʳ n) goal<n+fuel))
conf≡n (suc fuel) n config f goal goal<n+fuel n≤goal config≡false config≡true with n <? goal
... | yes n<goal
  rewrite config≡false n n<goal
  = conf≡n fuel (suc n) config f goal
    (ℕ.≤-trans goal<n+fuel (ℕ.≤-reflexive (ℕ.+-suc n fuel)))
    n<goal config≡false config≡true
... | no n≮goal
  rewrite ℕ.≤-antisym n≤goal (ℕ.≮⇒≥ n≮goal)
  rewrite config≡true
  = refl

conf>n :
  ∀ fuel n config f goal
  → goal < n + fuel
  → n ≤ goal
  → (∀ k → k < goal → config (f , k) ≡ false)
  → config (f , goal) ≡ false
  → goal < conf' fuel n config f
conf>n zero n config f goal goal<n+fuel n≤goal config≡false config≡false'
  = ⊥-elim (ℕ.≤⇒≯ n≤goal (proj₁ ℕ.<-resp₂-≡ (ℕ.+-identityʳ n) goal<n+fuel))
conf>n (suc fuel) n config f goal goal<n+fuel n≤goal config≡false config≡false' with n <? goal
... | yes n<goal
  rewrite config≡false n n<goal
  = conf>n fuel (suc n) config f goal
    (ℕ.≤-trans goal<n+fuel (ℕ.≤-reflexive (ℕ.+-suc n fuel)))
    n<goal config≡false config≡false'
... | no n≮goal
  rewrite ℕ.≤-antisym n≤goal (ℕ.≮⇒≥ n≮goal)
  rewrite config≡false'
  = lemma fuel (suc goal)
  where
  lemma : ∀ fuel n → n ≤ conf' fuel n config f
  lemma zero n = ℕ.≤-refl
  lemma (suc fuel) n with config (f , n)
  lemma (suc fuel) n | true = ℕ.≤-refl
  lemma (suc fuel) n | false = ℕ.≤-trans (ℕ.n≤1+n n) (lemma fuel (suc n))

translate-preserves-⊆ : ∀ {i : Size} {A : 𝔸} → {nadt : NADT F V i A} → (m : ℕ) → ChoiceArity≤ m nadt → ADT.⟦ translate nadt ⟧ ⊆[ conf m ] NADT.⟦ nadt ⟧
translate-preserves-⊆ m (leaf v) config = refl
translate-preserves-⊆ {A = A} m (choice f c cs cs≤m ChoiceArity-cs) config = go zero c cs cs≤m (λ where k ()) ChoiceArity-cs
  where
  go : ∀ {i : Size} → (n : ℕ) → (c : NADT F V i A) → (cs : List (NADT F V i A))
    → n + length (c ∷ cs) ≤ m
    → (∀ (k : ℕ) → k < n → config (f , k) ≡ false)
    → All (ChoiceArity≤ m) (c ∷ cs)
    → ADT.⟦ translate-cs f n c cs ⟧ config
    ≡ NADT.⟦ find-or-last (conf m config f ∸ n) (c ∷ cs) ⟧ (conf m config)
  go n c [] n+cs≤m config≡false (ChoiceArity≤-c ∷ []) =
      ADT.⟦ translate-cs f n c [] ⟧ config
    ≡⟨⟩
      ADT.⟦ translate c ⟧ config
    ≡⟨ translate-preserves-⊆ m ChoiceArity≤-c config ⟩
      NADT.⟦ c ⟧ (conf m config)
    ≡⟨⟩
      NADT.⟦ find-or-last (conf m config f ∸ n) (c ∷ []) ⟧ (conf m config)
    ∎
    where
    open Eq.≡-Reasoning
  go n c₁ (c₂ ∷ cs) n+cs≤m config≡false (ChoiceArity≤-c₁ ∷ ChoiceArity≤-cs) with config (f , n) in config-f
  go n c₁ (c₂ ∷ cs) n+cs≤m config≡false (ChoiceArity≤-c₁ ∷ ChoiceArity≤-cs) | true =
      ADT.⟦ translate c₁ ⟧ config
    ≡⟨ translate-preserves-⊆ m ChoiceArity≤-c₁ config ⟩
      NADT.⟦ c₁ ⟧ (conf m config)
    ≡⟨⟩
      NADT.⟦ find-or-last zero (c₁ ∷ c₂ ∷ cs) ⟧ (conf m config)
    ≡⟨ Eq.cong (λ x → NADT.⟦ find-or-last x (c₁ ∷ c₂ ∷ cs) ⟧ (conf m config)) {zero} {conf m config f ∸ n} (
      begin
        0
      ≡⟨ ℕ.n∸n≡0 n ⟨
        n ∸ n
      ≡⟨ Eq.cong (_∸ n) (conf≡n m zero config f n n<m z≤n config≡false config-f) ⟨
        conf m config f ∸ n
      ∎)
    ⟩
      NADT.⟦ find-or-last (conf m config f ∸ n) (c₁ ∷ c₂ ∷ cs) ⟧ (conf m config)
    ∎
    where
    n<m : n < m
    n<m =
      begin-strict
        n
      ≡⟨ ℕ.+-identityʳ n ⟨
        n + 0
      <⟨ ℕ.+-monoʳ-< n (s≤s z≤n) ⟩
        n + length (c₁ ∷ c₂ ∷ cs)
      ≤⟨ n+cs≤m ⟩
        m
      ∎
      where
      open ℕ.≤-Reasoning
    open Eq.≡-Reasoning
  go n c₁ (c₂ ∷ cs) n+cs≤m config≡false (ChoiceArity≤-c₁ ∷ ChoiceArity≤-cs) | false =
      ADT.⟦ translate-cs f (suc n) c₂ cs ⟧ config
    ≡⟨ go (suc n) c₂ cs (ℕ.≤-trans (ℕ.≤-reflexive (Eq.sym (ℕ.+-suc n (length (c₂ ∷ cs))))) n+cs≤m) config≡false' ChoiceArity≤-cs ⟩
      NADT.⟦ find-or-last (conf m config f ∸ suc n) (c₂ ∷ cs) ⟧ (conf m config)
    ≡⟨ Eq.cong (λ x → NADT.⟦ find-or-last (conf m config f ∸ x) (c₂ ∷ cs) ⟧ (conf m config)) (ℕ.+-comm 1 n) ⟩
      NADT.⟦ find-or-last (conf m config f ∸ (n + 1)) (c₂ ∷ cs) ⟧ (conf m config)
    ≡⟨ Eq.cong (λ x → NADT.⟦ find-or-last x (c₂ ∷ cs) ⟧ (conf m config)) (ℕ.∸-+-assoc (conf m config f) n 1) ⟨
      NADT.⟦ find-or-last (conf m config f ∸ n ∸ 1) (c₂ ∷ cs) ⟧ (conf m config)
    ≡⟨ Eq.cong (λ x → NADT.⟦ x ⟧ (conf m config)) (List.find-or-last-prepend-∸ {n = conf m config f ∸ n} (c₁ ∷ []) (c₂ ∷ cs) lemma) ⟨
      NADT.⟦ find-or-last (conf m config f ∸ n) (c₁ ∷ c₂ ∷ cs) ⟧ (conf m config)
    ∎
    where
    config≡false' : ∀ k → k < suc n → config (f , k) ≡ false
    config≡false' k k<n with k ≟ n
    config≡false' k k<n | yes refl = config-f
    config≡false' k k<n | no k≢n = config≡false k (ℕ.≤∧≢⇒< (ℕ.≤-pred k<n) k≢n)

    lemma : List⁺.length (c₁ ∷ []) ≤ conf m config f ∸ n
    lemma =
      begin
        List⁺.length (c₁ ∷ [])
      ≡⟨⟩
        1
      ≡⟨ Eq.cong suc (ℕ.n∸n≡0 n) ⟨
        suc (n ∸ n)
      ≡⟨ ℕ.+-∸-assoc 1 {n} {n} ℕ.≤-refl ⟨
        suc n ∸ n
      ≤⟨ ℕ.∸-monoˡ-≤ n (conf>n m zero config f n (
        begin-strict
          n
        ≡⟨ ℕ.+-identityʳ n ⟨
          n + 0
        <⟨ ℕ.+-monoʳ-< n (s≤s z≤n) ⟩
          n + length (c₁ ∷ c₂ ∷ cs)
        ≤⟨ n+cs≤m ⟩
          m
        ∎) z≤n config≡false config-f)
      ⟩
        conf m config f ∸ n
      ∎
      where
      open ℕ.≤-Reasoning

    open Eq.≡-Reasoning

translate-preserves-⊇ : ∀ {A : 𝔸} → (nadt : NADT F V ∞ A) → NADT.⟦ nadt ⟧ ⊆[ fnoc ] ADT.⟦ translate nadt ⟧
translate-preserves-⊇ (NADT.leaf v) config = refl
translate-preserves-⊇ {A} (f NADT.⟨ c ∷ cs ⟩) config = go zero c cs
  where
  go : (n : ℕ) → (c : NADT F V ∞ A) → (cs : List (NADT F V ∞ A)) → NADT.⟦ find-or-last (config f ∸ n) (c ∷ cs) ⟧ config ≡ ADT.⟦ translate-cs f n c cs ⟧ (fnoc config)
  go n c [] = translate-preserves-⊇ c config
  go n c₁ (c₂ ∷ cs) with config f ≤? n in config-f≤n-proof
  go n c₁ (c₂ ∷ cs) | yes config-f≤n =
      NADT.⟦ find-or-last (config f ∸ n) (c₁ ∷ c₂ ∷ cs) ⟧ config
    ≡⟨ Eq.cong (λ x → NADT.⟦ find-or-last x (c₁ ∷ c₂ ∷ cs) ⟧ config) (ℕ.m≤n⇒m∸n≡0 config-f≤n) ⟩
      NADT.⟦ find-or-last zero (c₁ ∷ c₂ ∷ cs) ⟧ config
    ≡⟨⟩
      NADT.⟦ c₁ ⟧ config
    ≡⟨ translate-preserves-⊇ c₁ config ⟩
      ADT.⟦ translate c₁ ⟧ (fnoc config)
    ≡⟨⟩
      (if true then ADT.⟦ translate c₁ ⟧ (fnoc config) else ADT.⟦ translate-cs f (suc n) c₂ cs ⟧ (fnoc config) )
    ≡⟨ Eq.cong (if_then ADT.⟦ translate c₁ ⟧ (fnoc config) else ADT.⟦ translate-cs f (suc n) c₂ cs ⟧ (fnoc config)) (Eq.cong does config-f≤n-proof) ⟨
      (if fnoc config (f , n) then ADT.⟦ translate c₁ ⟧ (fnoc config) else ADT.⟦ translate-cs f (suc n) c₂ cs ⟧ (fnoc config) )
    ≡⟨⟩
      ADT.⟦ (f , n) ADT.ADT.⟨ translate c₁ , translate-cs f (suc n) c₂ cs ⟩ ⟧ (fnoc config)
    ≡⟨⟩
      ADT.⟦ translate-cs f n c₁ (c₂ ∷ cs) ⟧ (fnoc config)
    ∎
    where
    open Eq.≡-Reasoning
  go n c₁ (c₂ ∷ cs) | no config-f≰n =
      NADT.⟦ find-or-last (config f ∸ n) (c₁ ∷ c₂ ∷ cs) ⟧ config
    ≡⟨ Eq.cong (λ x → NADT.⟦ x ⟧ config) (List.find-or-last-prepend-∸ {n = config f ∸ n} (c₁ ∷ []) (c₂ ∷ cs) fnoc-lemma) ⟩
      NADT.⟦ find-or-last ((config f ∸ n) ∸ 1) (c₂ ∷ cs) ⟧ config
    ≡⟨ Eq.cong (λ x → NADT.⟦ find-or-last x (c₂ ∷ cs) ⟧ config) (ℕ.∸-+-assoc (config f) n 1) ⟩
      NADT.⟦ find-or-last (config f ∸ (n + 1)) (c₂ ∷ cs) ⟧ config
    ≡⟨ Eq.cong (λ x → NADT.⟦ find-or-last (config f ∸ x) (c₂ ∷ cs) ⟧ config) (ℕ.+-comm n 1) ⟩
      NADT.⟦ find-or-last (config f ∸ suc n) (c₂ ∷ cs) ⟧ config
    ≡⟨ go (suc n) c₂ cs ⟩
      ADT.⟦ translate-cs f (suc n) c₂ cs ⟧ (fnoc config)
    ≡⟨⟩
      (if false then ADT.⟦ translate c₁ ⟧ (fnoc config) else ADT.⟦ translate-cs f (suc n) c₂ cs ⟧ (fnoc config) )
    ≡⟨ Eq.cong (if_then ADT.⟦ translate c₁ ⟧ (fnoc config) else ADT.⟦ translate-cs f (suc n) c₂ cs ⟧ (fnoc config)) (Eq.cong does config-f≤n-proof) ⟨
      (if fnoc config (f , n) then ADT.⟦ translate c₁ ⟧ (fnoc config) else ADT.⟦ translate-cs f (suc n) c₂ cs ⟧ (fnoc config))
    ≡⟨⟩
      ADT.⟦ (f , n) ADT.ADT.⟨ translate c₁ , translate-cs f (suc n) c₂ cs ⟩ ⟧ (fnoc config)
    ≡⟨⟩
      ADT.⟦ translate-cs f n c₁ (c₂ ∷ cs) ⟧ (fnoc config)
    ∎
    where
    fnoc-lemma : List⁺.length (c₁ ∷ []) Data.Nat.≤ config f ∸ n
    fnoc-lemma =
      begin
        List⁺.length (c₁ ∷ [])
      ≡⟨⟩
        1
      ≡⟨ Eq.cong suc (ℕ.n∸n≡0 n) ⟨
        suc (n ∸ n)
      ≡⟨ ℕ.+-∸-assoc 1 {n} ℕ.≤-refl ⟨
        suc n ∸ n
      ≤⟨ ℕ.∸-monoˡ-≤ n (ℕ.≰⇒> config-f≰n) ⟩
        config f ∸ n
      ∎
      where
      open ℕ.≤-Reasoning
    open Eq.≡-Reasoning

translate-preserves : ∀ {A : 𝔸} → (nadt : NADT F V ∞ A) → ADT.⟦ translate nadt ⟧ ≅[ conf ⌈ nadt ⌉ ][ fnoc ] NADT.⟦ nadt ⟧
translate-preserves nadt = translate-preserves-⊆ ⌈ nadt ⌉ (ChoiceArity≤-⌈⌉ nadt) , translate-preserves-⊇ nadt

lemma : ∀ {i : Size} {A : 𝔸} → (nadt : NADT F V i A) → sizeADT sizeV (translate nadt) ≤ 2 * sizeNADT sizeV nadt ∸ 1
lemma {A = A} (NADT.leaf v) =
  begin
    sizeADT sizeV (translate (NADT.NADT.leaf v))
  ≡⟨⟩
    sizeNADT {V = V} sizeV (NADT.NADT.leaf {F = F} v)
  ≡⟨⟩
    suc (sizeV v)
  ≡⟨⟩
    2 + sizeV v ∸ 1
  ≡⟨ Eq.cong (λ x → 2 + x ∸ 1) (ℕ.*-identityˡ (sizeV v)) ⟨
    2 + 1 * sizeV v ∸ 1
  ≤⟨ ℕ.∸-monoˡ-≤ 1 (ℕ.+-monoʳ-≤ 2 (ℕ.*-monoˡ-≤ (sizeV v) (s≤s (z≤n {1})))) ⟩
    2 + 2 * sizeV v ∸ 1
  ≡⟨ Eq.cong (_∸ 1) (ℕ.*-distribˡ-+ 2 1 (sizeV v)) ⟨
    2 * suc (sizeV v) ∸ 1
  ≡⟨⟩
    2 * sizeNADT {V = V} sizeV (NADT.NADT.leaf {F = F} v) ∸ 1
  ∎
  where
  open ℕ.≤-Reasoning
lemma {A = A} (f NADT.⟨ c ∷ cs ⟩) =
  begin
    sizeADT sizeV (translate (f NADT.NADT.⟨ c ∷ cs ⟩))
  ≡⟨⟩
    sizeADT sizeV (translate-cs f zero c cs)
  ≤⟨ go zero c cs ⟩
    2 * sum (map (sizeNADT sizeV) (c ∷ cs))
  ≤⟨ ℕ.n≤1+n (2 * sum (map (sizeNADT sizeV) (c ∷ cs))) ⟩
    1 + 2 * sum (map (sizeNADT sizeV) (c ∷ cs))
  ≡⟨⟩
    (2 + 2 * sum (map (sizeNADT sizeV) (c ∷ cs))) ∸ 1
  ≡⟨ Eq.cong (_∸ 1) (ℕ.*-distribˡ-+ 2 1 (sum (map (sizeNADT sizeV) (c ∷ cs)))) ⟨
    2 * suc (sum (map (sizeNADT sizeV) (c ∷ cs))) ∸ 1
  ≡⟨⟩
    2 * suc (sum (map (sizeNADT sizeV) (c ∷ cs))) ∸ 1
  ≡⟨⟩
    2 * sizeNADT sizeV (f NADT.NADT.⟨ c ∷ cs ⟩) ∸ 1
  ∎
  where
  open ℕ.≤-Reasoning

  go : ∀ {i : Size} → (n : ℕ) → (c : NADT F V i A) → (cs : List (NADT F V i A))
    → sizeADT sizeV (translate-cs f n c cs)
    ≤ 2 * sum (map (sizeNADT sizeV) (c ∷ cs))
  go n c [] =
    begin
      sizeADT sizeV (translate-cs f n c [])
    ≡⟨⟩
      sizeADT sizeV (translate c)
    ≤⟨ lemma c ⟩
      2 * sizeNADT sizeV c ∸ 1
    ≤⟨ ℕ.m∸n≤m (2 * sizeNADT sizeV c) 1 ⟩
      2 * sizeNADT sizeV c
    ≡⟨ Eq.cong (2 *_) (ℕ.+-identityʳ (sizeNADT sizeV c)) ⟨
      2 * (sizeNADT sizeV c + 0)
    ≡⟨⟩
      2 * sum (map (sizeNADT sizeV) (c ∷ []))
    ∎
  go n c₁ (c₂ ∷ cs) =
    begin
      sizeADT sizeV (translate-cs f n c₁ (c₂ ∷ cs))
    ≡⟨⟩
      sizeADT sizeV ((f , n) ADT.ADT.⟨ translate c₁ , translate-cs f (suc n) c₂ cs ⟩)
    ≡⟨⟩
      suc (sizeADT sizeV (translate c₁) + sizeADT sizeV (translate-cs f (suc n) c₂ cs))
    ≤⟨ ℕ.+-monoˡ-≤ (sizeADT sizeV (translate-cs f (suc n) c₂ cs)) (s≤s (lemma c₁)) ⟩
      suc (2 * sizeNADT sizeV c₁ ∸ 1) + sizeADT sizeV (translate-cs f (suc n) c₂ cs)
    ≤⟨ ℕ.+-monoʳ-≤ (suc (2 * sizeNADT sizeV c₁ ∸ 1)) (go (suc n) c₂ cs) ⟩
      suc (2 * sizeNADT sizeV c₁ ∸ 1) + 2 * sum (map (sizeNADT sizeV) (c₂ ∷ cs))
    ≡⟨ Eq.cong (_+ 2 * sum (map (sizeNADT sizeV) (c₂ ∷ cs))) (ℕ.+-∸-assoc 1 {2 * sizeNADT sizeV c₁} {1} (ℕ.≤-trans (sizeNADT>0 sizeV c₁) (ℕ.m≤n*m (sizeNADT sizeV c₁) 2))) ⟨
      2 * sizeNADT sizeV c₁ + 2 * sum (map (sizeNADT sizeV) (c₂ ∷ cs))
    ≡⟨ ℕ.*-distribˡ-+ 2 (sizeNADT sizeV c₁) (sum (map (sizeNADT sizeV) (c₂ ∷ cs))) ⟨
      2 * (sizeNADT sizeV c₁ + sum (map (sizeNADT sizeV) (c₂ ∷ cs)))
    ≡⟨⟩
      2 * sum (map (sizeNADT sizeV) (c₁ ∷ c₂ ∷ cs))
    ∎

ADT≤NADT : SizedADT (F × ℕ) V sizeV ≤ₛ SizedNADT F V sizeV
ADT≤NADT .proj₁ = 2
ADT≤NADT .proj₂ A e₂ e₂-translatable = translate e₂ , ≅[]→≅ (translate-preserves e₂) , ℕ.≤-trans (lemma e₂) (ℕ.m∸n≤m (2 * sizeNADT sizeV e₂) 1)
