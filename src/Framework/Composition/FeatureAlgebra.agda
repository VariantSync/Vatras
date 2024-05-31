{-
This module implements the feature algebra by Apel et al. in
"An Algebraic Foundation for Automatic Feature-based Program Synthesis",
SCP, 2010, Elsevier.

We noticed that there are two variants of the distant idempotence law depending
on the order of composition. In case the same artifact is composed from the left
and the right, one of these artifacts will determine the position in the result.
If the position of the left is prioritized over the right one, we call it
`LeftAdditive` otherwise we call it `RightAdditive`.
^- TODO ibbem: I am also not yet sure about these names.
               Just googling "left additive" did not really show something
               expect for some advanced category theory beyond the
               things we do here.
               What about just referring to these modules/algebras as
               "Left" and "Right" for now?
               Also, see my comment below. It might help to better
               understand what x should be in a name left-x / right-x.
               Other name ideas: x-dominant, x-determined,, x-override.
  @pmbittner: I like x-dominant the most out of the current ideas.
-}
module Framework.Composition.FeatureAlgebra where

open import Data.Product using (proj₁; proj₂; _×_; _,_; swap)
open import Algebra.Structures using (IsMonoid; IsSemigroup; IsMagma)
open import Algebra.Core using (Op₂)
open import Algebra.Definitions using (Associative; Commutative)
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
      -- ^- TODO ibbem: Is this really true?
      --                The ⊕ operator is right-associative (infixr)
      --                so the idempotence law is
      --                  i₁ ⊕ (i₂ ⊕ i₁) ≡ i₁ ⊕ i₂
      --                right?
      --                This means the leftmost occurence determines the order of introductions
      --                but i₁ is actually already part of the of the (i₂ ⊕ i₁) introduction, right?
      --                This means that introducing an introduction i₁ to an introduction (i₂ ⊕ i₁)
      --                it is already contained in, may still change/mutate the introduction because
      --                        i₂ ⊕ i₁  ≢ i₁ ⊕ i₂
      --                but
      --                  i₁ ⊕ (i₂ ⊕ i₁) ≡ i₁ ⊕ i₂
      --                If you like to, we could discuss this next week.
      -- @pmbittner: Regardless of the associativity, the leftmost occurence of
      --             `i₁` is the same in either case. However, I agree that the
      --             reasoning "has been introduced first" is wrong.
      --             On that note: I think it would make sense to use left
      --             associativity for LeftAdditive. It feels more intuitive in
      --             this case and is also more efficient. 😄 (The intuitive
      --             implementation traverses the right argument and inserts it
      --             into the left argument. The other way around is harder to
      --             implement.) In the end, it doesn't matter for us though,
      --             because we have associativity.
      --             A meeting next week sounds good to me.
      --
      --             A completely different thought I just had:
      --             There is actually more than one way to implement
      --             LeftDominant and RightDominant (now these names really
      --             start to make sense) than just the `flip` one I implemented
      --             below:
      --             (For simplicity, I ignore children in the following
      --             examples.)
      --
      --             1. LeftDominant (FST):
      --               (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ⊕ (5 ∷ 6 ∷ 2 ∷ 1 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ []
      --
      --             2. RightDominant (left→right FST):
      --               (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ⊕ (5 ∷ 6 ∷ 2 ∷ 1 ∷ []) ≡ 5 ∷ 6 ∷ 2 ∷ 1 ∷ 3 ∷ 4 ∷ []
      --
      --             3. alternative RightDominant:
      --               (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ⊕ (5 ∷ 6 ∷ 2 ∷ 1 ∷ []) ≡ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 2 ∷ 1 ∷ []
      --
      --             4. alternative LeftDominant (right→left of the previous one):
      --               (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ⊕ (5 ∷ 6 ∷ 2 ∷ 1 ∷ []) ≡ 5 ∷ 6 ∷ 1 ∷ 2 ∷ 3 ∷ 4 []
      --
      --             If you are unsure what the 3ʳᵈ version is doing, think of
      --             the following:
      --             1. l ⊕ r = mergeDuplicatesIntoLeftmost (l ++ r)
      --             2. l ⊕ r = mergeDuplicatesIntoLeftmost (r ++ l)
      --             3. l ⊕ r = mergeDuplicatesIntoRightmost (l ++ r)
      --             4. l ⊕ r = mergeDuplicatesIntoRightmost (r ++ l)
      --
      --             Thinking about it, 3 is way more intuitive than 2 (maybe
      --             even "trivial" 😂).
      --
      --             Currently, I can't think of a simple way to convert 1 or 2
      --             into 3 or 4 without having implementation knowledge.
      --             However, for FSTs, mirroring the variant (visually, on the
      --             y-axis) before and after the composition seems to work.
      --             e.g. 3. l ⊕ r = mirror (mergeDuplicatesIntoRightmost (mirror (l ++ r)))
      --             with
      --             mirror fs = map mirror' (reverse fs)
      --             mirror' (a -< cs >-) = a -< mirror cs >-
      --
      --
      -- This is, duplicates of i have no effect.
      -- ^- TODO ibbem: So this is wrong, right?
      -- @pmbittner: Yes, strictly speaking. I think a better explanation would
      --             be "This is, additional introductions on the right have no
      --             effect."
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

{-|
This is the feature algebra as introduced initially by Apel et al.
-}
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

commutativity : ∀ {c} (I : Set c) (_⊕_ : Op₂ I) (𝟘 : I)
  → LeftAdditive.FeatureAlgebra I _⊕_ 𝟘
  → RightAdditive.FeatureAlgebra I _⊕_ 𝟘
  → Commutative _≡_ _⊕_
commutativity I _⊕_ 𝟘 faˡ faʳ a b =
    a ⊕ b
  ≡⟨ LeftAdditive.FeatureAlgebra.distant-idempotence faˡ a b ⟨
    a ⊕ (b ⊕ a)
  ≡⟨ RightAdditive.FeatureAlgebra.distant-idempotence faʳ b a ⟩
    b ⊕ a
  ∎
  where
  open Eq.≡-Reasoning

open LeftAdditive.FeatureAlgebra
open RightAdditive.FeatureAlgebra
open IsMonoid
open IsSemigroup
open IsMagma

left→right : ∀ {c} (I : Set c) (sum : Op₂ I) (𝟘 : I)
  → LeftAdditive.FeatureAlgebra I sum 𝟘
  → RightAdditive.FeatureAlgebra I (flip sum) 𝟘
left→right I sum 𝟘 faˡ = record
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

right→left : ∀ {c} (I : Set c) (sum : Op₂ I) (𝟘 : I)
  → RightAdditive.FeatureAlgebra I sum 𝟘
  → LeftAdditive.FeatureAlgebra I (flip sum) 𝟘
right→left I sum 𝟘 faʳ = record
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

module _ where
  {-
  To prove that `left→right` and `right→left` are inverses
  we need to prove that their function compositions
  keep the feature algebra composition operation and
  the laws unchanged.

  The feature algebra composition operation is judgementally equal.
  However, the proof that the laws are unchanged requires
  extensionality because many of these laws are functions and
  uniqueness of identity proofs (K axiom) because the result of these functions are equalities.

  To limit the scope of these axioms, an unnamed modules is used.
  -}
  open import Axioms.Extensionality
  open import Relation.Binary.PropositionalEquality.WithK using (≡-irrelevant)

  isInverse : ∀ {c} (I : Set c) (sum : Op₂ I) (𝟘 : I)
    → IsInverse _≡_ _≡_ (left→right I (flip sum) 𝟘) (right→left I sum 𝟘)
  isInverse I sum 𝟘 = record
    { isLeftInverse = record
      { isCongruent = record
        { cong = Eq.cong (left→right I (flip sum) 𝟘)
        ; isEquivalence₁ = Eq.isEquivalence
        ; isEquivalence₂ = Eq.isEquivalence
        }
      ; from-cong = Eq.cong (right→left I sum 𝟘)
      ; inverseˡ = invˡ
      }
    ; inverseʳ = invʳ
    }
    where
    open Eq.≡-Reasoning

    invˡ : Inverseˡ _≡_ _≡_ (left→right I (flip sum) 𝟘) (right→left I sum 𝟘)
    invˡ {faˡ} x rewrite x =
        left→right I (flip sum) 𝟘 (right→left I sum 𝟘 faˡ)
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

    invʳ : Inverseʳ _≡_ _≡_ (left→right I (flip sum) 𝟘) (right→left I sum 𝟘)
    invʳ {faʳ} x rewrite x =
        right→left I sum 𝟘 (left→right I (flip sum) 𝟘 faʳ)
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
