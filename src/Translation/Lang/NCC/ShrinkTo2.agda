{-# OPTIONS --sized-types #-}

open import Framework.Definitions using (𝕍)
open import Framework.Construct using (_∈ₛ_; cons)
open import Construct.Artifact as At using () renaming (Syntax to Artifact; _-<_>- to artifact-constructor)

{-
This module defines a compiler from NCC n to NCC 2.
To do so, each choice with n alternatives (a ∷ as) is replaced by a binary choice
between the first alternative a and a recursively reduced choice for as.
The results looks like this:

  D ⟨ a , b , c , d ⟩
            ↓
  D.0 ⟨ a , D.1 ⟨ b , D.2 ⟨ c , d ⟩ ⟩ ⟩
-}
module Translation.Lang.NCC.ShrinkTo2 (Variant : 𝕍) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

open import Data.Empty using (⊥-elim)
import Data.EqIndexedSet as IndexedSet
open import Data.Fin as Fin using (Fin; zero; suc)
import Data.Fin.Properties as Fin
open import Data.List as List using (List; []; _∷_)
import Data.List.Properties as List
open import Data.Nat using (ℕ; zero; suc; _<_; s≤s; z≤n; _+_; _∸_)
open import Data.Nat.Properties as ℕ using (≤-refl; ≤-reflexive; ≤-trans; <-trans)
open import Data.Product using (_×_; _,_)
open import Data.Vec as Vec using (Vec; []; _∷_)
import Data.Vec.Properties as Vec
open import Framework.Compiler using (LanguageCompiler; _⊕_)
open import Framework.Definitions using (𝔸; 𝔽)
open import Framework.Relation.Function using (from; to)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl; _≗_)
open import Relation.Nullary.Decidable using (yes; no)
open import Size using (Size; ∞)
import Util.AuxProofs as ℕ
open import Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs)
import Util.Vec as Vec

open Eq.≡-Reasoning using (step-≡; step-≡˘; _≡⟨⟩_; _∎)
open IndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-sym)

open import Lang.All.Generic Variant Artifact∈ₛVariant
open NCC using (NCC; NCCL; _-<_>-; _⟨_⟩)

artifact : {A : 𝔸} → A → List (Variant A) → Variant A
artifact a cs = cons Artifact∈ₛVariant (artifact-constructor a cs)

-- To simplify the implementation and the proof, we constrain the translation to result in 2-ary `NCC` expressions.
-- The idea of the translation is to represent each alternative vector as a `List` of alternatives where each `c ∷ cs` is represented by an alternative `d ⟨ c ∷ cs ∷ [] ⟩`.
-- However, this requires that each dimension `d` in this list of alternatives can be configured independently.
-- Otherwise only the first, or last alternative can be selected by configuring `d`.
-- The solution is to extend the dimension `d` by an index (`IndexedDimension`) which numbers the list of alternatives.
-- Note that the last choice in the list of alternatives holds two alternatives, so there will be one less dimension index than there are alternatives.
open import Framework.Annotation.IndexedDimension

shrinkTo2 : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
  → (n : ℕ≥ 2)
  → NCC n D i A
  → NCC (sucs zero) (IndexedDimension D n) ∞ A
shrinkTo2 n (a -< cs >-) = a -< List.map (shrinkTo2 n) cs >-
shrinkTo2 {i} {D} {A} (sucs n) (d ⟨ cs ⟩) = go n (ℕ.n<1+n n) cs
  module shrinkTo2-Implementation where
  go : {i : Size} → (m : ℕ) → (m≤n : m < suc n) → Vec (NCC (sucs n) D i A) (suc (suc m)) → NCC (sucs zero) (D × Fin (suc n)) ∞ A
  go zero m≤n (l ∷ r ∷ []) = (d , Fin.opposite (Fin.fromℕ< {zero} m≤n)) ⟨ shrinkTo2 (sucs n) l ∷ shrinkTo2 (sucs n) r ∷ [] ⟩
  go (suc m) m≤n (c ∷ cs) = (d , Fin.opposite (Fin.fromℕ< {suc m} m≤n)) ⟨ shrinkTo2 (sucs n) c ∷ go m (<-trans (ℕ.n<1+n m) m≤n) cs ∷ [] ⟩

conf : ∀ {D : 𝔽}
  → (n : ℕ≥ 2)
  → NCC.Configuration n D
  → NCC.Configuration (sucs zero) (IndexedDimension D n)
conf (sucs n) config (d , m) with config d Fin.≟ (Fin.inject₁ m)
... | yes _ = zero
... | no _ = suc zero

module ConfLemmas where
  config≡0' : ∀ {D : 𝔽} {d : D} {n : ℕ}
    → (config : NCC.Configuration (sucs n) D)
    → (j : Fin (suc n))
    → config d ≡ (Fin.inject₁ j)
    → conf (sucs n) config (d , j) ≡ zero
  config≡0' {d = d} config j config-d≡j with config d Fin.≟ (Fin.inject₁ j)
  ... | yes _ = refl
  ... | no config-d≢j = ⊥-elim (config-d≢j config-d≡j)

  config≡1' : ∀ {D : 𝔽} {d : D} {n : ℕ}
    → (config : NCC.Configuration (sucs n) D)
    → (j : Fin (suc n))
    → config d ≢ (Fin.inject₁ j)
    → conf (sucs n) config (d , j) ≡ suc zero
  config≡1' {d = d} config j config-d≢j with config d Fin.≟ (Fin.inject₁ j)
  ... | yes config-d≡j = ⊥-elim (config-d≢j config-d≡j)
  ... | no _ = refl

fnoc : ∀ {D : 𝔽}
  → (n : ℕ≥ 2)
  → NCC.Configuration (sucs zero) (IndexedDimension D n)
  → NCC.Configuration n D
fnoc (sucs n) config d = go n (ℕ.n<1+n n)
  module fnoc-Implementation where
  go : (m : ℕ) → m < suc n → Fin (suc (suc n))
  go m m<n with config (d , Fin.opposite (Fin.fromℕ< {m} m<n))
  go m m<n | zero = Fin.inject₁ (Fin.opposite (Fin.fromℕ< {m} m<n))
  go zero m<n | suc zero = Fin.fromℕ (suc n)
  go (suc m) m<n | suc zero = go m (<-trans (ℕ.n<1+n m) m<n)

module FnocLemmas where
  config≡0 : ∀ {D : 𝔽} {d : D} {n : ℕ}
    → (config : NCC.Configuration (sucs zero) (D × Fin (suc n)))
    → (j : Fin (suc n))
    → fnoc (sucs n) config d ≡ Fin.inject₁ j
    → config (d , j) ≡ zero
  config≡0 {d = d} {n = n} config j config≡j = go' n (ℕ.n<1+n n) config≡j
    where
    open fnoc-Implementation

    go' : (m : ℕ) → (m<n : m < suc n) → go n config d m m<n ≡ Fin.inject₁ j → config (d , j) ≡ zero
    go' m m<n go≡j with config (d , Fin.opposite (Fin.fromℕ< {m} m<n)) in config-opposite-m
    go' m m<n go≡j | zero = Eq.trans (Eq.cong config (Eq.cong₂ _,_ refl (Eq.sym (Fin.inject₁-injective go≡j)))) config-opposite-m
    go' zero m<n go≡j | suc zero = ⊥-elim (Fin.toℕ-inject₁-≢ j (Eq.trans (Eq.sym (Fin.toℕ-fromℕ (suc n))) (Eq.cong Fin.toℕ go≡j)))
    go' (suc m) m<n go≡j | suc zero = go' m (<-trans (ℕ.n<1+n m) m<n) go≡j

  config≡1 : ∀ {D : 𝔽} {d : D} {n : ℕ}
    → (config : NCC.Configuration (sucs zero) (D × Fin (suc n)))
    → (j : Fin (suc n))
    → j Fin.< fnoc (sucs n) config d
    → config (d , j) ≡ suc zero
  config≡1 {d = d} {n = n} config j config<j = go' n (ℕ.n<1+n n) config<j (λ k<opposite-n → ⊥-elim (ℕ.n≮0 (≤-trans k<opposite-n (≤-reflexive (Eq.trans (Fin.opposite-prop (Fin.fromℕ< (ℕ.n<1+n n))) (Eq.trans (Eq.cong₂ _∸_ refl (Fin.toℕ-fromℕ< (ℕ.n<1+n n))) (ℕ.n∸n≡0 n)))))))
    where
    open fnoc-Implementation

    extend-∀config≡1
      : {m : ℕ}
      → (m<n : suc m < suc n)
      → config (d , Fin.opposite (Fin.fromℕ< {suc m} m<n)) ≡ suc zero
      → (∀ {k} → k Fin.< Fin.opposite (Fin.fromℕ< {suc m}                      m<n ) → config (d , k) ≡ suc zero)
      → (∀ {k} → k Fin.< Fin.opposite (Fin.fromℕ< {    m} (<-trans (ℕ.n<1+n m) m<n)) → config (d , k) ≡ suc zero)
    extend-∀config≡1 {m} m<n config≡1 ∀config≡1 {k} m<k with k Fin.≟ Fin.opposite (Fin.fromℕ< {suc m} m<n)
    ... | yes k≡m = Eq.trans (Eq.cong config (Eq.cong₂ _,_ refl k≡m)) config≡1
    ... | no k≢m = ∀config≡1 (ℕ.≤∧≢⇒< (ℕ.≤-pred (≤-trans m<k (≤-reflexive (Eq.trans (Fin.opposite-prop (Fin.fromℕ< (<-trans (s≤s ≤-refl) m<n))) (Eq.trans (Eq.cong₂ _∸_ refl (Fin.toℕ-fromℕ< (<-trans (s≤s ≤-refl) m<n))) (Eq.trans (ℕ.+-∸-assoc 1 (ℕ.≤-pred m<n)) (Eq.cong suc (Eq.sym (Eq.trans (Fin.opposite-prop (Fin.fromℕ< m<n)) (Eq.cong₂ _∸_ refl (Fin.toℕ-fromℕ< m<n))))))))))) (k≢m ∘ Fin.toℕ-injective))

    go' : (m : ℕ)
      → (m<n : m < suc n)
      → j Fin.< go n config d m m<n
      → (∀ {k : Fin (suc n)}
      → k Fin.< Fin.opposite (Fin.fromℕ< {m} m<n)
      → config (d , k) ≡ suc zero) → config (d , j) ≡ suc zero
    go' m m<n j<go ∀config≡1 with config (d , Fin.opposite (Fin.fromℕ< {m} m<n)) in config-opposite-m
    go' m m<n j<go ∀config≡1 | zero with Fin.opposite (Fin.fromℕ< {m} m<n) Fin.≤? j
    go' m m<n j<go ∀config≡1 | zero | yes m≤j = ⊥-elim (ℕ.n≮n (Fin.toℕ j) (≤-trans j<go (≤-trans (≤-reflexive (Fin.toℕ-inject₁ (Fin.opposite (Fin.fromℕ< m<n)))) m≤j)))
    go' m m<n j<go ∀config≡1 | zero | no m≰j = ∀config≡1 (ℕ.≰⇒> m≰j)
    go' m m<n j<go ∀config≡1 | suc zero with j Fin.≟ Fin.opposite (Fin.fromℕ< {m} m<n)
    go' m m<n j<go ∀config≡1 | suc zero | yes j≡m = Eq.trans (Eq.cong config (Eq.cong₂ _,_ refl j≡m)) config-opposite-m
    go' zero m<n j<go ∀config≡1 | suc zero | no j≢m = ∀config≡1 (ℕ.≤∧≢⇒< (≤-trans (ℕ.≤-pred (Fin.toℕ<n j)) (≤-reflexive (Eq.sym (Eq.trans (Fin.opposite-prop (Fin.fromℕ< m<n)) (Eq.cong₂ _∸_ refl (Fin.toℕ-fromℕ< m<n)))))) (j≢m ∘ Fin.toℕ-injective))
    go' (suc m) m<n j<go ∀config≡1 | suc zero | no j≢m = go' m (<-trans (ℕ.n<1+n m) m<n) j<go (extend-∀config≡1 {m = m} m<n config-opposite-m ∀config≡1)

preserves-⊆ : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
  → (n : ℕ≥ 2)
  → (expr : NCC n D i A)
  → NCC.⟦ shrinkTo2 n expr ⟧ ⊆[ fnoc n ] NCC.⟦ expr ⟧
preserves-⊆ (sucs n) (a -< cs >-) config =
    NCC.⟦ shrinkTo2 (sucs n) (a -< cs >-) ⟧ config
  ≡⟨⟩
    NCC.⟦ a -< List.map (shrinkTo2 (sucs n)) cs >- ⟧ config
  ≡⟨⟩
    artifact a (List.map (λ e → NCC.⟦ e ⟧ config) (List.map (shrinkTo2 (sucs n)) cs))
  ≡˘⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
    artifact a (List.map (λ e → NCC.⟦ shrinkTo2 (sucs n) e ⟧ config) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊆ (sucs n) e config) cs) ⟩
    artifact a (List.map (λ e → NCC.⟦ e ⟧ (fnoc (sucs n) config)) cs)
  ≡⟨⟩
    NCC.⟦ a -< cs >- ⟧ (fnoc (sucs n) config)
  ∎
preserves-⊆ {D = D} {A = A} (sucs n) (d ⟨ cs ⟩) config =
    NCC.⟦ shrinkTo2 (sucs n) (d ⟨ cs ⟩) ⟧ config
  ≡⟨ lemma n (ℕ.n<1+n n) cs (fnoc (sucs n) config d) (ℕ.+-comm n (Fin.toℕ (fnoc (sucs n) config d))) ⟩
    NCC.⟦ Vec.lookup cs (fnoc (sucs n) config d) ⟧ (fnoc (sucs n) config)
  ≡⟨⟩
    NCC.⟦ d ⟨ cs ⟩ ⟧ (fnoc (sucs n) config)
  ∎
  where
  open shrinkTo2-Implementation

  -- The key to this lemma, which is an induction over `m`, is to introduce a
  -- number `j` which enables stating the invariant provided as the last
  -- argument:
  --   `m + Fin.toℕ (fnoc (sucs n) config d) ≡ Fin.toℕ j + n`
  -- It states that the alternative which is `j` choices deep is selected. At
  -- the start of the induction (`m ≡ n`), `j` is determined by the
  -- configuration, specifically `fnoc (sucs n) config d`. In each step of the
  -- induction both `m` and `j` are decreased so the invariant is obeyed.
  -- Hence, as base cases of the induction, we have the cases where `m ≡ zero`
  -- or `j ≡ zero`. In all cases we can inspect `j` to conclude if the first
  -- (`j ≡ zero`) or second (`j > zero`) alternative is chosen, which is all
  -- that is needed to conclude the proof.
  lemma
    : {i : Size}
    → (m : ℕ)
    → (m≤n : m < suc n)
    → (cs' : Vec (NCC (sucs n) D i A) (suc (suc m)))
    → (j : Fin (suc (suc m)))
    → m + Fin.toℕ (fnoc (sucs n) config d) ≡ Fin.toℕ j + n
    → NCC.⟦ go n d cs m m≤n cs' ⟧ config ≡ NCC.⟦ Vec.lookup cs' j ⟧ (fnoc (sucs n) config)
  lemma zero m≤n (l ∷ r ∷ []) zero m+config-d≡j+n =
      NCC.⟦ go n d cs zero m≤n (l ∷ r ∷ []) ⟧ config
    ≡⟨⟩
      NCC.⟦ (d , Fin.opposite (Fin.fromℕ< {zero} m≤n)) ⟨ shrinkTo2 (sucs n) l ∷ shrinkTo2 (sucs n) r ∷ [] ⟩ ⟧ config
    ≡⟨⟩
      NCC.⟦ Vec.lookup (shrinkTo2 (sucs n) l ∷ shrinkTo2 (sucs n) r ∷ []) (config (d , Fin.opposite (Fin.fromℕ< {zero} m≤n))) ⟧ config
    ≡⟨ Eq.cong₂ NCC.⟦_⟧ (Eq.cong₂ Vec.lookup {x = shrinkTo2 (sucs n) l ∷ shrinkTo2 (sucs n) r ∷ []} refl (FnocLemmas.config≡0 config (Fin.opposite (Fin.fromℕ< m≤n)) (Fin.toℕ-injective (Eq.trans m+config-d≡j+n (Eq.trans (Eq.sym (Fin.toℕ-fromℕ n)) (Eq.trans (Eq.cong Fin.toℕ (Eq.cong Fin.opposite (Eq.sym (Fin.fromℕ<-toℕ zero m≤n)))) (Eq.sym (Fin.toℕ-inject₁ (Fin.opposite (Fin.fromℕ< m≤n)))))))))) refl ⟩
      NCC.⟦ Vec.lookup (shrinkTo2 (sucs n) l ∷ shrinkTo2 (sucs n) r ∷ []) zero ⟧ config
    ≡⟨⟩
      NCC.⟦ shrinkTo2 (sucs n) l ⟧ config
    ≡⟨ preserves-⊆ (sucs n) l config ⟩
      NCC.⟦ l ⟧ (fnoc (sucs n) config)
    ∎
  lemma zero m≤n (l ∷ r ∷ []) (suc zero) m+config-d≡j+n =
      NCC.⟦ (d , Fin.opposite (Fin.fromℕ< m≤n)) ⟨ shrinkTo2 (sucs n) l ∷ shrinkTo2 (sucs n) r ∷ [] ⟩ ⟧ config
    ≡⟨⟩
      NCC.⟦ Vec.lookup (shrinkTo2 (sucs n) l ∷ shrinkTo2 (sucs n) r ∷ []) (config (d , Fin.opposite (Fin.fromℕ< m≤n))) ⟧ config
    ≡⟨ Eq.cong₂ NCC.⟦_⟧ (Eq.cong₂ Vec.lookup {x = shrinkTo2 (sucs n) l ∷ shrinkTo2 (sucs n) r ∷ []} refl (FnocLemmas.config≡1 config (Fin.opposite (Fin.fromℕ< m≤n))
      (let module ≤ = ℕ.≤-Reasoning in
        ≤.begin-strict
          Fin.toℕ (Fin.opposite (Fin.fromℕ< m≤n))
        ≤.≡⟨ Fin.opposite-prop (Fin.fromℕ< m≤n) ⟩
          n ∸ Fin.toℕ (Fin.fromℕ< m≤n)
        ≤.≡⟨ Eq.cong₂ _∸_ refl (Fin.toℕ-fromℕ< m≤n) ⟩
        n
        ≤.<⟨ ℕ.n<1+n n ⟩
          suc n
        ≤.≡˘⟨ m+config-d≡j+n ⟩
          Fin.toℕ (fnoc (sucs n) config d)
        ≤.∎
      ))) refl ⟩
      NCC.⟦ shrinkTo2 (sucs n) r ⟧ config
    ≡⟨ preserves-⊆ (sucs n) r config ⟩
      NCC.⟦ r ⟧ (fnoc (sucs n) config)
    ∎
  lemma (suc m) m≤n (c ∷ cs') zero m+config-d≡j+n =
      NCC.⟦ (d , Fin.opposite (Fin.fromℕ< m≤n)) ⟨ shrinkTo2 (sucs n) c ∷ go n d cs m (<-trans (ℕ.n<1+n m) m≤n) cs' ∷ [] ⟩ ⟧ config
    ≡⟨ Eq.cong₂ NCC.⟦_⟧ (Eq.cong₂ Vec.lookup {x = shrinkTo2 (sucs n) c ∷ go n d cs m (<-trans (ℕ.n<1+n m) m≤n) cs' ∷ []} refl (FnocLemmas.config≡0 config (Fin.opposite (Fin.fromℕ< {suc m} m≤n)) (Fin.toℕ-injective (
          Fin.toℕ (fnoc (sucs n) config d)
        ≡˘⟨ ℕ.m+n∸m≡n (suc m) (Fin.toℕ (fnoc (sucs n) config d)) ⟩
          suc m + Fin.toℕ (fnoc (sucs n) config d) ∸ suc m
        ≡⟨ Eq.cong (λ n → n ∸ suc m) m+config-d≡j+n ⟩
          n ∸ suc m
        ≡˘⟨ Eq.cong₂ _∸_ refl (Fin.toℕ-fromℕ< m≤n) ⟩
          n ∸ (Fin.toℕ (Fin.fromℕ< m≤n))
        ≡˘⟨ Fin.opposite-prop (Fin.fromℕ< m≤n) ⟩
          Fin.toℕ (Fin.opposite (Fin.fromℕ< m≤n))
        ≡˘⟨ Fin.toℕ-inject₁ (Fin.opposite (Fin.fromℕ< m≤n)) ⟩
          Fin.toℕ (Fin.inject₁ (Fin.opposite (Fin.fromℕ< m≤n)))
        ∎
      )))) refl ⟩
      NCC.⟦ shrinkTo2 (sucs n) c ⟧ config
    ≡⟨ preserves-⊆ (sucs n) c config ⟩
      NCC.⟦ c ⟧ (fnoc (sucs n) config)
    ∎
  lemma (suc m) (s≤s m≤n) (c ∷ cs') (suc j) m+config-d≡j+n =
      NCC.⟦ (d , Fin.opposite (Fin.fromℕ< (s≤s m≤n))) ⟨ shrinkTo2 (sucs n) c ∷ go n d cs m (<-trans (ℕ.n<1+n m) (s≤s m≤n)) cs' ∷ [] ⟩ ⟧ config
    ≡⟨ Eq.cong₂ NCC.⟦_⟧ (Eq.cong₂ Vec.lookup {x = shrinkTo2 (sucs n) c ∷ go n d cs m (<-trans (ℕ.n<1+n m) (s≤s m≤n)) cs' ∷ []} refl (FnocLemmas.config≡1 config (Fin.opposite (Fin.fromℕ< (s≤s m≤n)))
      (let module ≤ = ℕ.≤-Reasoning in
        ≤.begin-strict
          Fin.toℕ (Fin.inject₁ (Fin.opposite (Fin.fromℕ< m≤n)))
        ≤.≡⟨ Fin.toℕ-inject₁ (Fin.opposite (Fin.fromℕ< m≤n)) ⟩
          Fin.toℕ (Fin.opposite (Fin.fromℕ< m≤n))
        ≤.≡⟨ Fin.opposite-prop (Fin.fromℕ< m≤n) ⟩
          n ∸ suc (Fin.toℕ (Fin.fromℕ< m≤n))
        ≤.≡⟨ Eq.cong₂ _∸_ {x = n} refl (Eq.cong suc (Fin.toℕ-fromℕ< m≤n)) ⟩
        n ∸ suc m
        ≤.<⟨ ℕ.m≤n⇒m≤o+n (Fin.toℕ j) (ℕ.m∸n≢0⇒n<m (ℕ.m>n⇒m∸n≢0 (ℕ.n∸1+m<n∸m m≤n))) ⟩
          Fin.toℕ j + (n ∸ m)
        ≤.≡˘⟨ ℕ.+-∸-assoc (Fin.toℕ j) (ℕ.≤-pred (ℕ.m≤n⇒m≤1+n m≤n)) ⟩
          Fin.toℕ j + n ∸ m
        ≤.≡⟨⟩
          suc (Fin.toℕ j + n) ∸ suc m
        ≤.≡˘⟨ Eq.cong (λ n → n ∸ suc m) m+config-d≡j+n ⟩
          suc m + Fin.toℕ (fnoc (sucs n) config d) ∸ suc m
        ≤.≡⟨ ℕ.m+n∸m≡n (suc m) (Fin.toℕ (fnoc (sucs n) config d)) ⟩
          Fin.toℕ (fnoc (sucs n) config d)
        ≤.∎
      ))) refl ⟩
      NCC.⟦ go n d cs m (<-trans (ℕ.n<1+n m) (s≤s m≤n)) cs' ⟧ config
    ≡⟨ lemma m (<-trans (ℕ.n<1+n m) (s≤s m≤n)) cs' j (ℕ.suc-injective m+config-d≡j+n) ⟩
      NCC.⟦ Vec.lookup cs' j ⟧ (fnoc (sucs n) config)
    ∎

preserves-⊇ : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
  → (n : ℕ≥ 2)
  → (expr : NCC n D i A)
  → NCC.⟦ expr ⟧ ⊆[ conf n ] NCC.⟦ shrinkTo2 n expr ⟧
preserves-⊇ (sucs n) (a -< cs >-) config =
    NCC.⟦ a -< cs >- ⟧ config
  ≡⟨⟩
    artifact a (List.map (λ e → NCC.⟦ e ⟧ config) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊇ (sucs n) e config) cs) ⟩
    artifact a (List.map (λ z → NCC.⟦ shrinkTo2 (sucs n) z ⟧ (conf (sucs n) config)) cs)
  ≡⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
    artifact a (List.map (λ e → NCC.⟦ e ⟧ (conf (sucs n) config)) (List.map (shrinkTo2 (sucs n)) cs))
  ≡⟨⟩
    NCC.⟦ shrinkTo2 (sucs n) (a -< cs >-) ⟧ (conf (sucs n) config)
  ∎
preserves-⊇ {D = D} {A = A} (sucs n) (d ⟨ cs ⟩) config =
    NCC.⟦ d ⟨ cs ⟩ ⟧ config
  ≡⟨⟩
    NCC.⟦ Vec.lookup cs (config d) ⟧ config
  ≡˘⟨ lemma n (ℕ.n<1+n n) cs (config d) (ℕ.+-comm n (Fin.toℕ (config d))) ⟩
    NCC.⟦ shrinkTo2 (sucs n) (d ⟨ cs ⟩) ⟧ (conf (sucs n) config)
  ∎
  where
  open shrinkTo2-Implementation

  -- The key to this lemma, which is an induction over `m`, is to introduce a
  -- number `j` which enables stating the invariant provided as the last
  -- argument:
  --   `m + Fin.toℕ (config d) ≡ Fin.toℕ j + n`
  -- It states that the alternative which is `j` choices deep is selected. At
  -- the start of the induction (`m ≡ n`), `j` is determined by the
  -- configuration, specifically `config d`. In each step of the
  -- induction both `m` and `j` are decreased so the invariant is obeyed.
  -- Hence, as base cases of the induction, we have the cases where `m ≡ zero`
  -- or `j ≡ zero`. In all cases we can inspect `j` to conclude if the first
  -- (`j ≡ zero`) or second (`j > zero`) alternative is chosen, which is all
  -- that is needed to conclude the proof
  lemma
    : {i : Size}
    → (m : ℕ)
    → (m≤n : m < suc n)
    → (cs' : Vec (NCC (sucs n) D i A) (suc (suc m)))
    → (j : Fin (suc (suc m)))
    → m + Fin.toℕ (config d) ≡ Fin.toℕ j + n
    → NCC.⟦ go n d cs m m≤n cs' ⟧ (conf (sucs n) config) ≡ NCC.⟦ Vec.lookup cs' j ⟧ config
  lemma zero m≤n (l ∷ r ∷ []) zero m+config-d≡j+n =
      NCC.⟦ go n d cs zero m≤n (l ∷ r ∷ []) ⟧ (conf (sucs n) config)
    ≡⟨⟩
      NCC.⟦ (d , Fin.opposite (Fin.fromℕ< {zero} m≤n)) ⟨ shrinkTo2 (sucs n) l ∷ shrinkTo2 (sucs n) r ∷ [] ⟩ ⟧ (conf (sucs n) config)
    ≡⟨⟩
      NCC.⟦ Vec.lookup (shrinkTo2 (sucs n) l ∷ shrinkTo2 (sucs n) r ∷ []) (conf (sucs n) config (d , Fin.opposite (Fin.fromℕ< {zero} m≤n))) ⟧ (conf (sucs n) config)
    ≡⟨ Eq.cong₂ NCC.⟦_⟧ (Eq.cong₂ Vec.lookup {x = shrinkTo2 (sucs n) l ∷ shrinkTo2 (sucs n) r ∷ []} refl (ConfLemmas.config≡0' config (Fin.opposite (Fin.fromℕ< m≤n)) (Fin.toℕ-injective (
          Fin.toℕ (config d)
        ≡⟨ m+config-d≡j+n ⟩
          n
        ≡˘⟨ Fin.toℕ-fromℕ n ⟩
          Fin.toℕ (Fin.fromℕ n)
        ≡⟨ Eq.cong Fin.toℕ (Eq.cong Fin.opposite (Eq.sym (Fin.fromℕ<-toℕ zero m≤n))) ⟩
          Fin.toℕ (Fin.opposite (Fin.fromℕ< m≤n))
        ≡˘⟨ Fin.toℕ-inject₁ (Fin.opposite (Fin.fromℕ< m≤n)) ⟩
          Fin.toℕ (Fin.inject₁ (Fin.opposite (Fin.fromℕ< m≤n)))
        ∎
      )))) refl ⟩
      NCC.⟦ Vec.lookup (shrinkTo2 (sucs n) l ∷ shrinkTo2 (sucs n) r ∷ []) zero ⟧ (conf (sucs n) config)
    ≡⟨⟩
      NCC.⟦ shrinkTo2 (sucs n) l ⟧ (conf (sucs n) config)
    ≡˘⟨ preserves-⊇ (sucs n) l config ⟩
      NCC.⟦ l ⟧ config
    ∎
  lemma zero m≤n (l ∷ r ∷ []) (suc zero) m+config-d≡j+n =
      NCC.⟦ (d , Fin.opposite (Fin.fromℕ< m≤n)) ⟨ shrinkTo2 (sucs n) l ∷ shrinkTo2 (sucs n) r ∷ [] ⟩ ⟧ (conf (sucs n) config)
    ≡⟨⟩
      NCC.⟦ Vec.lookup (shrinkTo2 (sucs n) l ∷ shrinkTo2 (sucs n) r ∷ []) (conf (sucs n) config (d , Fin.opposite (Fin.fromℕ< m≤n))) ⟧ (conf (sucs n) config)
    ≡⟨ Eq.cong₂ NCC.⟦_⟧ (Eq.cong₂ Vec.lookup {x = shrinkTo2 (sucs n) l ∷ shrinkTo2 (sucs n) r ∷ []} refl (ConfLemmas.config≡1' config (Fin.opposite (Fin.fromℕ< m≤n)) (λ config-d≡opposite-m → ℕ.1+n≢n (
          suc n
        ≡˘⟨ m+config-d≡j+n ⟩
          Fin.toℕ (config d)
        ≡⟨ Eq.cong Fin.toℕ config-d≡opposite-m ⟩
          Fin.toℕ (Fin.inject₁ (Fin.opposite (Fin.fromℕ< m≤n)))
        ≡⟨ Fin.toℕ-inject₁ (Fin.opposite (Fin.fromℕ< m≤n)) ⟩
          Fin.toℕ (Fin.opposite (Fin.fromℕ< m≤n))
        ≡⟨ Fin.opposite-prop (Fin.fromℕ< m≤n) ⟩
          n ∸ Fin.toℕ (Fin.fromℕ< m≤n)
        ≡⟨ Eq.cong₂ _∸_ refl (Fin.toℕ-fromℕ< m≤n) ⟩
          n ∸ zero
        ≡⟨⟩
          n
        ∎
      )))) refl ⟩
      NCC.⟦ shrinkTo2 (sucs n) r ⟧ (conf (sucs n) config)
    ≡˘⟨ preserves-⊇ (sucs n) r config ⟩
      NCC.⟦ r ⟧ config
    ∎
  lemma (suc m) m≤n (c ∷ cs') zero m+config-d≡j+n =
      NCC.⟦ (d , Fin.opposite (Fin.fromℕ< m≤n)) ⟨ shrinkTo2 (sucs n) c ∷ go n d cs m (<-trans (ℕ.n<1+n m) m≤n) cs' ∷ [] ⟩ ⟧ (conf (sucs n) config)
    ≡⟨ Eq.cong₂ NCC.⟦_⟧ (Eq.cong₂ Vec.lookup {x = shrinkTo2 (sucs n) c ∷ go n d cs m (<-trans (ℕ.n<1+n m) m≤n) cs' ∷ []} refl (ConfLemmas.config≡0' config (Fin.opposite (Fin.fromℕ< m≤n)) (Fin.toℕ-injective (
          Fin.toℕ (config d)
        ≡˘⟨ ℕ.m+n∸m≡n (suc m) (Fin.toℕ (config d)) ⟩
          suc m + Fin.toℕ (config d) ∸ suc m
        ≡⟨ Eq.cong (λ n → n ∸ suc m) m+config-d≡j+n ⟩
          n ∸ suc m
        ≡˘⟨ Eq.cong₂ _∸_ refl (Fin.toℕ-fromℕ< m≤n) ⟩
          n ∸ (Fin.toℕ (Fin.fromℕ< m≤n))
        ≡˘⟨ Fin.opposite-prop (Fin.fromℕ< m≤n) ⟩
          Fin.toℕ (Fin.opposite (Fin.fromℕ< m≤n))
        ≡˘⟨ Fin.toℕ-inject₁ (Fin.opposite (Fin.fromℕ< m≤n)) ⟩
          Fin.toℕ (Fin.inject₁ (Fin.opposite (Fin.fromℕ< m≤n)))
        ∎
      )))) refl ⟩
      NCC.⟦ shrinkTo2 (sucs n) c ⟧ (conf (sucs n) config)
    ≡˘⟨ preserves-⊇ (sucs n) c config ⟩
      NCC.⟦ c ⟧ config
    ∎
  lemma (suc m) (s≤s m≤n) (c ∷ cs') (suc j) m+config-d≡j+n =
      NCC.⟦ (d , Fin.opposite (Fin.fromℕ< (s≤s m≤n))) ⟨ shrinkTo2 (sucs n) c ∷ go n d cs m (<-trans (ℕ.n<1+n m) (s≤s m≤n)) cs' ∷ [] ⟩ ⟧ (conf (sucs n) config)
    ≡⟨ Eq.cong₂ NCC.⟦_⟧ (Eq.cong₂ Vec.lookup {x = shrinkTo2 (sucs n) c ∷ go n d cs m (<-trans (ℕ.n<1+n m) (s≤s m≤n)) cs' ∷ []} refl (ConfLemmas.config≡1' config (Fin.opposite (Fin.fromℕ< (s≤s m≤n)))
      (λ config-d≡opposite-m → (ℕ.<⇒≢ (ℕ.m≤n⇒m≤o+n (Fin.toℕ j) (ℕ.m∸n≢0⇒n<m (ℕ.m>n⇒m∸n≢0 (ℕ.n∸1+m<n∸m m≤n))))) (
          n ∸ suc m
        ≡˘⟨ Eq.cong₂ _∸_ {x = n} refl (Eq.cong suc (Fin.toℕ-fromℕ< m≤n)) ⟩
          n ∸ suc (Fin.toℕ (Fin.fromℕ< m≤n))
        ≡˘⟨ Fin.opposite-prop (Fin.fromℕ< m≤n) ⟩
          Fin.toℕ (Fin.opposite (Fin.fromℕ< m≤n))
        ≡˘⟨ Fin.toℕ-inject₁ (Fin.opposite (Fin.fromℕ< m≤n)) ⟩
          Fin.toℕ (Fin.inject₁ (Fin.opposite (Fin.fromℕ< m≤n)))
        ≡˘⟨ Fin.toℕ-inject₁ (Fin.inject₁ (Fin.opposite (Fin.fromℕ< m≤n))) ⟩
          Fin.toℕ (Fin.inject₁ (Fin.inject₁ (Fin.opposite (Fin.fromℕ< m≤n))))
        ≡˘⟨ Eq.cong Fin.toℕ config-d≡opposite-m ⟩
          Fin.toℕ (config d)
        ≡˘⟨ ℕ.m+n∸m≡n (suc m) (Fin.toℕ (config d)) ⟩
          suc m + Fin.toℕ (config d) ∸ suc m
        ≡⟨⟩
          m + Fin.toℕ (config d) ∸ m
        ≡⟨ Eq.cong (λ n → n ∸ suc m) m+config-d≡j+n ⟩
          Fin.toℕ j + n ∸ m
        ≡⟨ ℕ.+-∸-assoc (Fin.toℕ j) (ℕ.≤-pred (ℕ.m≤n⇒m≤1+n m≤n)) ⟩
          Fin.toℕ j + (n ∸ m)
        ∎
      )))) refl ⟩
      NCC.⟦ go n d cs m (<-trans (ℕ.n<1+n m) (s≤s m≤n)) cs' ⟧ (conf (sucs n) config)
    ≡⟨ lemma m (<-trans (ℕ.n<1+n m) (s≤s m≤n)) cs' j (ℕ.suc-injective m+config-d≡j+n) ⟩
      NCC.⟦ Vec.lookup cs' j ⟧ config
    ∎

preserves : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
  → (n : ℕ≥ 2)
  → (expr : NCC n D i A)
  → NCC.⟦ shrinkTo2 n expr ⟧ ≅[ fnoc n ][ conf n ] NCC.⟦ expr ⟧
preserves n expr = preserves-⊆ n expr , preserves-⊇ n expr

shrinkTo2Compiler : ∀ {i : Size} {D : 𝔽} → (n : ℕ≥ 2) → LanguageCompiler (NCCL {i} n D) (NCCL (sucs zero) (D × Fin (ℕ≥.toℕ (ℕ≥.pred n))))
shrinkTo2Compiler n .LanguageCompiler.compile = shrinkTo2 n
shrinkTo2Compiler n .LanguageCompiler.config-compiler expr .to = conf n
shrinkTo2Compiler n .LanguageCompiler.config-compiler expr .from = fnoc n
shrinkTo2Compiler n .LanguageCompiler.preserves expr = ≅[]-sym (preserves n expr)
