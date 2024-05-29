{-
This module implements the feature algebra by Apel et al.

We noticed that there are two variants of the distant idempotence law depending
on the order of composition. In case the same artifact is composed from the left
and the right, one of them will determine the position in the result. If the
position of the left is prioritized over the right one, we call it
`LeftAdditive` otherwise we call it `RightAdditive`.
-}
module Framework.Composition.FeatureAlgebra where

open import Data.Product using (proj₁; proj₂; _×_; _,_; swap)
open import Algebra.Structures using (IsMonoid; IsSemigroup; IsMagma)
open import Algebra.Core using (Op₂)
open import Algebra.Definitions using (Associative)
open import Function using (flip; IsInverse; Inverseˡ; Inverseʳ)
open import Relation.Binary using (Rel; Reflexive; Symmetric; Transitive; IsEquivalence; IsPreorder)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Level using (suc; _⊔_)

module LeftAdditive where
  record FeatureAlgebra {c} (I : Set c) (sum : Op₂ I) (𝟘 : I) : Set (suc c) where
    open Eq.≡-Reasoning

    _⊕_ = sum
    infixr 7 _⊕_

    field
      monoid : IsMonoid _≡_ _⊕_ 𝟘

      -- Only the leftmost occurence of an introduction is effective in a sum,
      -- because it has been introduced first.
      -- This is, duplicates of i have no effect.
      distant-idempotence : ∀ (i₁ i₂ : I) → i₁ ⊕ i₂ ⊕ i₁ ≡ i₁ ⊕ i₂

    open IsMonoid monoid

    direct-idempotence : ∀ (i : I) → i ⊕ i ≡ i
    direct-idempotence i =
      begin
        i ⊕ i
      ≡⟨ Eq.cong (i ⊕_) (proj₁ identity i) ⟨
        i ⊕ 𝟘 ⊕ i
      ≡⟨ distant-idempotence i 𝟘 ⟩
        i ⊕ 𝟘
      ≡⟨ proj₂ identity i ⟩
        i
      ∎

    -- introduction inclusion
    infix 6 _≤_
    _≤_ : Rel I c
    i₂ ≤ i₁ = i₁ ⊕ i₂ ≡ i₁

    ≤-refl : Reflexive _≤_
    ≤-refl {i} = direct-idempotence i

    ≤-trans : Transitive _≤_
    ≤-trans {i} {j} {k} i≤j j≤k =
      begin
        k ⊕ i
      ≡⟨ Eq.cong (_⊕ i) j≤k ⟨
        (k ⊕ j) ⊕ i
      ≡⟨ Eq.cong (λ x → (k ⊕ x) ⊕ i) i≤j ⟨
        (k ⊕ (j ⊕ i)) ⊕ i
      ≡⟨ assoc k (j ⊕ i) i ⟩
        k ⊕ ((j ⊕ i) ⊕ i)
      ≡⟨ Eq.cong (k ⊕_) (assoc j i i) ⟩
        k ⊕ (j ⊕ (i ⊕ i))
      ≡⟨ Eq.cong (k ⊕_) (Eq.cong (j ⊕_) (direct-idempotence i)) ⟩
        k ⊕ (j ⊕ i)
      ≡⟨ Eq.cong (k ⊕_) i≤j ⟩
        k ⊕ j
      ≡⟨ j≤k ⟩
        k
      ∎

    ≤-IsPreorder : IsPreorder _≡_ _≤_
    ≤-IsPreorder = record
      { isEquivalence = Eq.isEquivalence
      ; reflexive = λ where refl → ≤-refl
      ; trans = ≤-trans
      }

    least-element : ∀ i → 𝟘 ≤ i
    least-element = proj₂ identity

    least-element-unique : ∀ i → i ≤ 𝟘 → i ≡ 𝟘
    least-element-unique i i≤𝟘 rewrite (proj₁ identity i) = i≤𝟘

    upper-bound-l : ∀ i₂ i₁ → i₂ ≤ i₂ ⊕ i₁
    upper-bound-l i₂ i₁ =
      begin
        (i₂ ⊕ i₁) ⊕ i₂
      ≡⟨ assoc i₂ i₁ i₂ ⟩
        i₂ ⊕ (i₁ ⊕ i₂)
      ≡⟨ distant-idempotence i₂ i₁ ⟩
        i₂ ⊕ i₁
      ∎

    upper-bound-r : ∀ i₂ i₁ → i₁ ≤ i₂ ⊕ i₁
    upper-bound-r i₂ i₁ =
      begin
        (i₂ ⊕ i₁) ⊕ i₁
      ≡⟨ assoc i₂ i₁ i₁ ⟩
        i₂ ⊕ (i₁ ⊕ i₁)
      ≡⟨ Eq.cong (i₂ ⊕_) (direct-idempotence i₁) ⟩
        i₂ ⊕ i₁
      ∎

    least-upper-bound : ∀ i i₂ i₁
      → i₁ ≤ i
      → i₂ ≤ i
        -----------
      → i₁ ⊕ i₂ ≤ i
    least-upper-bound i i₂ i₁ i₁≤i i₂≤i =
      begin
        i ⊕ (i₁ ⊕ i₂)
      ≡⟨ assoc i i₁ i₂ ⟨
        (i ⊕ i₁) ⊕ i₂
      ≡⟨ Eq.cong (_⊕ i₂) i₁≤i ⟩
        i ⊕ i₂
      ≡⟨ i₂≤i ⟩
        i
      ∎

    -- introduction equivalence
    infix 6 _~_
    _~_ : Rel I c
    i₂ ~ i₁ = i₂ ≤ i₁ × i₁ ≤ i₂

    ~-refl : Reflexive _~_
    ~-refl = ≤-refl , ≤-refl

    ~-sym : Symmetric _~_
    ~-sym (fst , snd) = snd , fst

    ~-trans : Transitive _~_
    ~-trans (i≤j , j≤i) (j≤k , k≤j) = ≤-trans i≤j j≤k , ≤-trans k≤j j≤i

    ~-IsEquivalence : IsEquivalence _~_
    ~-IsEquivalence = record
      { refl  = ~-refl
      ; sym   = ~-sym
      ; trans = ~-trans
      }

    quasi-smaller : ∀ i₂ i₁ → i₂ ⊕ i₁ ≤ i₁ ⊕ i₂
    quasi-smaller i₂ i₁ =
      begin
        (i₁ ⊕ i₂) ⊕ (i₂ ⊕ i₁)
      ≡⟨ assoc (i₁ ⊕ i₂) i₂ i₁ ⟨
        ((i₁ ⊕ i₂) ⊕ i₂) ⊕ i₁
      ≡⟨ Eq.cong (_⊕ i₁) (assoc i₁ i₂ i₂) ⟩
        (i₁ ⊕ (i₂ ⊕ i₂)) ⊕ i₁
      ≡⟨ Eq.cong (_⊕ i₁) (Eq.cong (i₁ ⊕_) (direct-idempotence i₂)) ⟩
        (i₁ ⊕ i₂) ⊕ i₁
      ≡⟨ assoc i₁ i₂ i₁ ⟩
        i₁ ⊕ (i₂ ⊕ i₁)
      ≡⟨ distant-idempotence i₁ i₂ ⟩
        i₁ ⊕ i₂
      ∎

    quasi-commutativity : ∀ i₂ i₁ → i₂ ⊕ i₁ ~ i₁ ⊕ i₂
    quasi-commutativity i₂ i₁ = quasi-smaller i₂ i₁ , quasi-smaller i₁ i₂

module RightAdditive where
  record FeatureAlgebra {c} (I : Set c) (sum : Op₂ I) (𝟘 : I) : Set (suc c) where
    open Eq.≡-Reasoning

    _⊕_ = sum
    infixr 7 _⊕_

    field
      monoid : IsMonoid _≡_ _⊕_ 𝟘

      -- Only the rightmost occurence of an introduction is effective in a sum,
      -- because it has been introduced first.
      -- This is, duplicates of i have no effect.
      distant-idempotence : ∀ (i₁ i₂ : I) → i₂ ⊕ i₁ ⊕ i₂ ≡ i₁ ⊕ i₂

    open IsMonoid monoid

    direct-idempotence : ∀ (i : I) → i ⊕ i ≡ i
    direct-idempotence i =
      begin
        i ⊕ i
      ≡⟨ Eq.cong (i ⊕_) (proj₁ identity i) ⟨
        i ⊕ 𝟘 ⊕ i
      ≡⟨ distant-idempotence 𝟘 i ⟩
        𝟘 ⊕ i
      ≡⟨ proj₁ identity i ⟩
        i
      ∎

    -- introduction inclusion
    infix 6 _≤_
    _≤_ : Rel I c
    i₂ ≤ i₁ = i₂ ⊕ i₁ ≡ i₁

    ≤-refl : Reflexive _≤_
    ≤-refl {i} = direct-idempotence i

    ≤-trans : Transitive _≤_
    ≤-trans {i} {j} {k} i≤j j≤k =
      begin
        i ⊕ k
      ≡⟨ Eq.cong (i ⊕_) j≤k ⟨
        i ⊕ (j ⊕ k)
      ≡⟨ Eq.cong (λ x → i ⊕ x ⊕ k) i≤j ⟨
        i ⊕ ((i ⊕ j) ⊕ k)
      ≡⟨ assoc i (i ⊕ j) k ⟨
        (i ⊕ (i ⊕ j)) ⊕ k
      ≡⟨ Eq.cong (_⊕ k) (assoc i i j) ⟨
        ((i ⊕ i) ⊕ j) ⊕ k
      ≡⟨ Eq.cong (_⊕ k) (Eq.cong (_⊕ j) (direct-idempotence i)) ⟩
        (i ⊕ j) ⊕ k
      ≡⟨ Eq.cong (_⊕ k) i≤j ⟩
        j ⊕ k
      ≡⟨ j≤k ⟩
        k
      ∎

    ≤-IsPreorder : IsPreorder _≡_ _≤_
    ≤-IsPreorder = record
      { isEquivalence = Eq.isEquivalence
      ; reflexive = λ where refl → ≤-refl
      ; trans = ≤-trans
      }

    least-element : ∀ i → 𝟘 ≤ i
    least-element = proj₁ identity

    least-element-unique : ∀ i → i ≤ 𝟘 → i ≡ 𝟘
    least-element-unique i i≤𝟘 rewrite (proj₂ identity i) = i≤𝟘

    upper-bound-l : ∀ i₂ i₁ → i₂ ≤ i₂ ⊕ i₁
    upper-bound-l i₂ i₁ =
      begin
        i₂ ⊕ (i₂ ⊕ i₁)
      ≡⟨ Eq.sym (assoc i₂ i₂ i₁) ⟩
        (i₂ ⊕ i₂) ⊕ i₁
      ≡⟨ Eq.cong (_⊕ i₁) (direct-idempotence i₂) ⟩
        i₂ ⊕ i₁
      ∎

    upper-bound-r : ∀ i₂ i₁ → i₁ ≤ i₂ ⊕ i₁
    upper-bound-r i₂ i₁ = distant-idempotence i₂ i₁

    least-upper-bound : ∀ i i₂ i₁
      → i₁ ≤ i
      → i₂ ≤ i
        -----------
      → i₁ ⊕ i₂ ≤ i
    least-upper-bound i i₂ i₁ i₁≤i i₂≤i =
      begin
        (i₁ ⊕ i₂) ⊕ i
      ≡⟨ assoc i₁ i₂ i ⟩
        i₁ ⊕ (i₂ ⊕ i)
      ≡⟨ Eq.cong (i₁ ⊕_) i₂≤i ⟩
        i₁ ⊕ i
      ≡⟨ i₁≤i ⟩
        i
      ∎

    -- introduction equivalence
    infix 6 _~_
    _~_ : Rel I c
    i₂ ~ i₁ = i₂ ≤ i₁ × i₁ ≤ i₂

    ~-refl : Reflexive _~_
    ~-refl = ≤-refl , ≤-refl

    ~-sym : Symmetric _~_
    ~-sym (fst , snd) = snd , fst

    ~-trans : Transitive _~_
    ~-trans (i≤j , j≤i) (j≤k , k≤j) = ≤-trans i≤j j≤k , ≤-trans k≤j j≤i

    ~-IsEquivalence : IsEquivalence _~_
    ~-IsEquivalence = record
      { refl  = ~-refl
      ; sym   = ~-sym
      ; trans = ~-trans
      }

    quasi-smaller : ∀ i₂ i₁ → i₂ ⊕ i₁ ≤ i₁ ⊕ i₂
    quasi-smaller i₂ i₁ =
      begin
        (i₂ ⊕ i₁) ⊕ i₁ ⊕ i₂
      ≡⟨⟩
        (i₂ ⊕ i₁) ⊕ (i₁ ⊕ i₂)
      ≡⟨ assoc (i₂ ⊕ i₁) i₁ i₂ ⟨
        ((i₂ ⊕ i₁) ⊕ i₁) ⊕ i₂
      ≡⟨ Eq.cong (_⊕ i₂) (assoc i₂ i₁ i₁) ⟩
        (i₂ ⊕ (i₁ ⊕ i₁)) ⊕ i₂
      ≡⟨ Eq.cong (_⊕ i₂) (Eq.cong (i₂ ⊕_) (direct-idempotence i₁)) ⟩
        (i₂ ⊕ i₁) ⊕ i₂
      ≡⟨ assoc i₂ i₁ i₂ ⟩
        i₂ ⊕ i₁ ⊕ i₂
      ≡⟨ distant-idempotence i₁ i₂ ⟩
        i₁ ⊕ i₂
      ∎

    quasi-commutativity : ∀ i₂ i₁ → i₂ ⊕ i₁ ~ i₁ ⊕ i₂
    quasi-commutativity i₂ i₁ = quasi-smaller i₂ i₁ , quasi-smaller i₁ i₂

open LeftAdditive.FeatureAlgebra
open RightAdditive.FeatureAlgebra
open IsMonoid
open IsSemigroup
open IsMagma

to : ∀ {c} (I : Set c) (sum : Op₂ I) (𝟘 : I)
  → LeftAdditive.FeatureAlgebra I sum 𝟘
  → RightAdditive.FeatureAlgebra I (flip sum) 𝟘
to I sum 𝟘 faˡ = record
  { monoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = isEquivalence (isMagma (isSemigroup (monoid faˡ)))
        ; ∙-cong = flip (∙-cong (isMagma (isSemigroup (monoid faˡ))))
        }
      ; assoc = λ a b c → Eq.sym (assoc (isSemigroup (monoid faˡ)) c b a)
      }
    ; identity = swap (identity (monoid faˡ))
    }
  ; distant-idempotence = λ a b → Eq.trans (assoc (isSemigroup (monoid faˡ)) b a b) (distant-idempotence faˡ b a)
  }

from : ∀ {c} (I : Set c) (sum : Op₂ I) (𝟘 : I)
  → RightAdditive.FeatureAlgebra I sum 𝟘
  → LeftAdditive.FeatureAlgebra I (flip sum) 𝟘
from I sum 𝟘 faʳ = record
  { monoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = isEquivalence (isMagma (isSemigroup (monoid faʳ)))
        ; ∙-cong = flip (∙-cong (isMagma (isSemigroup (monoid faʳ))))
        }
      ; assoc = λ a b c → Eq.sym (assoc (isSemigroup (monoid faʳ)) c b a)
      }
    ; identity = swap (identity (monoid faʳ))
    }
  ; distant-idempotence = λ a b → Eq.trans (assoc (isSemigroup (monoid faʳ)) a b a) (distant-idempotence faʳ b a)
  }

open import Axioms.Extensionality
open import Relation.Binary.PropositionalEquality.WithK using (≡-irrelevant)

isInverse : ∀ {c} (I : Set c) (sum : Op₂ I) (𝟘 : I)
  → IsInverse _≡_ _≡_ (to I (flip sum) 𝟘) (from I sum 𝟘)
isInverse I sum 𝟘 = record
  { isLeftInverse = record
    { isCongruent = record
      { cong = Eq.cong (to I (flip sum) 𝟘)
      ; isEquivalence₁ = Eq.isEquivalence
      ; isEquivalence₂ = Eq.isEquivalence
      }
    ; from-cong = Eq.cong (from I sum 𝟘)
    ; inverseˡ = invˡ
    }
  ; inverseʳ = invʳ
  }
  where
  open Eq.≡-Reasoning

  invˡ : Inverseˡ _≡_ _≡_ (to I (flip sum) 𝟘) (from I sum 𝟘)
  invˡ {faˡ} x rewrite x =
      to I (flip sum) 𝟘 (from I sum 𝟘 faˡ)
    ≡⟨⟩
      record
        { monoid = record
          { isSemigroup = record
            { isMagma = record
              { isEquivalence = isEquivalence (isMagma (isSemigroup (monoid faˡ)))
              ; ∙-cong = flip (flip (∙-cong (isMagma (isSemigroup (monoid faˡ)))))
              }
            ; assoc = λ a b c → Eq.sym (Eq.sym (assoc (isSemigroup (monoid faˡ)) a b c))
            }
          ; identity = swap (swap (identity (monoid faˡ)))
          }
        ; distant-idempotence = λ a b → Eq.trans (Eq.sym (assoc (isSemigroup (monoid faˡ)) b a b)) (Eq.trans (assoc (isSemigroup (monoid faˡ)) b a b) (distant-idempotence faˡ a b))
        }
    ≡⟨⟩
      record
        { monoid = record
          { isSemigroup = record
            { isMagma = record
              { isEquivalence = isEquivalence (isMagma (isSemigroup (monoid faˡ)))
              ; ∙-cong = ∙-cong (isMagma (isSemigroup (monoid faˡ)))
              }
            ; assoc = λ a b c → Eq.sym (Eq.sym (assoc (isSemigroup (monoid faˡ)) a b c))
            }
          ; identity = identity (monoid faˡ)
          }
        ; distant-idempotence = λ a b → Eq.trans (Eq.sym (assoc (isSemigroup (monoid faˡ)) b a b)) (Eq.trans (assoc (isSemigroup (monoid faˡ)) b a b) (distant-idempotence faˡ a b))
        }
    ≡⟨ Eq.cong₂ (λ x y →
        record
          { monoid = record
            { isSemigroup = record
              { isMagma = record
                { isEquivalence = isEquivalence (isMagma (isSemigroup (monoid faˡ)))
                ; ∙-cong = ∙-cong (isMagma (isSemigroup (monoid faˡ)))
                }
              ; assoc = x
              }
            ; identity = identity (monoid faˡ)
            }
          ; distant-idempotence = y
          })
        (extensionality λ a → extensionality λ b → extensionality (λ c → ≡-irrelevant (Eq.sym (Eq.sym (assoc (isSemigroup (monoid faˡ)) a b c))) (assoc (isSemigroup (monoid faˡ)) a b c)))
        (extensionality λ a → extensionality λ b → ≡-irrelevant (Eq.trans (Eq.sym (assoc (isSemigroup (monoid faˡ)) b a b)) (Eq.trans (assoc (isSemigroup (monoid faˡ)) b a b) (distant-idempotence faˡ a b))) (distant-idempotence faˡ a b)) ⟩
      faˡ
    ∎

  invʳ : Inverseʳ _≡_ _≡_ (to I (flip sum) 𝟘) (from I sum 𝟘)
  invʳ {faʳ} x rewrite x =
      from I sum 𝟘 (to I (flip sum) 𝟘 faʳ)
    ≡⟨⟩
      record
        { monoid = record
          { isSemigroup = record
            { isMagma = record
              { isEquivalence = isEquivalence (isMagma (isSemigroup (monoid faʳ)))
              ; ∙-cong = flip (flip (∙-cong (isMagma (isSemigroup (monoid faʳ)))))
              }
            ; assoc = λ a b c → Eq.sym (Eq.sym (assoc (isSemigroup (monoid faʳ)) a b c))
            }
          ; identity = swap (swap (identity (monoid faʳ)))
          }
        ; distant-idempotence = λ a b → Eq.trans (Eq.sym (assoc (isSemigroup (monoid faʳ)) a b a)) (Eq.trans (assoc (isSemigroup (monoid faʳ)) a b a) (distant-idempotence faʳ a b))
        }
    ≡⟨⟩
      record
        { monoid = record
          { isSemigroup = record
            { isMagma = record
              { isEquivalence = isEquivalence (isMagma (isSemigroup (monoid faʳ)))
              ; ∙-cong = ∙-cong (isMagma (isSemigroup (monoid faʳ)))
              }
            ; assoc = λ a b c → Eq.sym (Eq.sym (assoc (isSemigroup (monoid faʳ)) a b c))
            }
          ; identity = identity (monoid faʳ)
          }
        ; distant-idempotence = λ a b → Eq.trans (Eq.sym (assoc (isSemigroup (monoid faʳ)) a b a)) (Eq.trans (assoc (isSemigroup (monoid faʳ)) a b a) (distant-idempotence faʳ a b))
        }
    ≡⟨ Eq.cong₂ (λ x y →
        record
          { monoid = record
            { isSemigroup = record
              { isMagma = record
                { isEquivalence = isEquivalence (isMagma (isSemigroup (monoid faʳ)))
                ; ∙-cong = ∙-cong (isMagma (isSemigroup (monoid faʳ)))
                }
              ; assoc = x
              }
            ; identity = identity (monoid faʳ)
            }
          ; distant-idempotence = y
          })
        (extensionality λ a → extensionality λ b → extensionality (λ c → ≡-irrelevant (Eq.sym (Eq.sym (assoc (isSemigroup (monoid faʳ)) a b c))) (assoc (isSemigroup (monoid faʳ)) a b c)))
        (extensionality λ a → extensionality λ b → ≡-irrelevant (Eq.trans (Eq.sym (assoc (isSemigroup (monoid faʳ)) a b a)) (Eq.trans (assoc (isSemigroup (monoid faʳ)) a b a) (distant-idempotence faʳ a b))) (distant-idempotence faʳ a b)) ⟩
      faʳ
    ∎
