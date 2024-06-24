{-
This module implements the feature algebra by Apel et al. in
"An Algebraic Foundation for Automatic Feature-based Program Synthesis",
SCP, 2010, Elsevier.

We noticed that there are two variants of the distant idempotence law depending
on the order of composition. In case the same artifact is composed from the left
and the right, one of these artifacts will determine the position in the result.
If the position of the left is prioritized over the right one, we call it
`LeftDominant` otherwise we call it `RightDominant`.
^- TODO ibbem: I am also not yet sure about these names.
               Just googling "left additive" did not really show something
               expect for some advanced category theory beyond the
               things we do here.
               What about just referring to these modules/algebras as
               "Left" and "Right" for now?
               Also, see my comment below. It might help to better
               understand what x should be in a name left-x / right-x.
               Other name ideas: x-dominant, x-determined, x-override.
  @pmbittner: I like x-dominant the most out of the current ideas.
  @ibbem:     Me too. Then let's stick with that for now.
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

module LeftDominant where
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
      --                but i₁ is actually already part of the (i₂ ⊕ i₁) introduction, right?
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
      --             associativity for LeftDominant. It feels more intuitive in
      --             this case and is also more efficient. 😄 (The intuitive
      --             implementation traverses the right argument and inserts it
      --             into the left argument. The other way around is harder to
      --             implement.) In the end, it doesn't matter for us though,
      --             because we have associativity.
      --             A meeting next week sounds good to me.
      -- @ibbem: Ah true, we have associativity, so we actually have:
      --                         i₂  ⊕ i₁  ≢ i₁ ⊕ i₂
      --                but
      --                   i₁ ⊕ (i₂  ⊕ i₁) ≡ i₁ ⊕ i₂
      --                and
      --                  (i₁ ⊕  i₂) ⊕ i₁  ≡ i₁ ⊕ i₂
      --         which means, the rightmost occurence has no effect, right!?
      --         It still is a bit counter-intuitive because without explicit
      --         brackets, i₁ ⊕ (i₂ ⊕ i₁) is still the order of computation, where
      --         the rightmost occurence is handled first but is only "later" found
      --         to have no effect. :thinking:


      -- @pmbittner: A completely different thought I just had:
      --             There is actually more than one way to implement
      --             LeftDominant and RightDominant (now these names really
      --             start to make sense) than just the `flip` one I implemented
      --             below:
      --             (For simplicity, I ignore children in the following
      --             examples.)
      --
      --             1. LeftDominant (FST):
      --               (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ⊕ (5 ∷ 6 ∷ 2 ∷ 1 ∷ []) ≡ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ []
      --     --> @ibbem: This is what you used for the proofs, right?
      --
      --             2. RightDominant (left→right FST):
      --               (1 ∷ 2 ∷ 3 ∷ 4 ∷ []) ⊕ (5 ∷ 6 ∷ 2 ∷ 1 ∷ []) ≡ 5 ∷ 6 ∷ 2 ∷ 1 ∷ 3 ∷ 4 ∷ []
      --     --> @ibbem: This is what I described in the paper and had formalized in Agda, right (except for the alternating-bug)?
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
      --     --> @ibbem: This formulation is brilliant! It helped a lot in understanding 3 and 4. Also, it is a great
      --                 explanation how and why these four alternative composition strategies exist!
      --                 I am yet unsure what to do with these results.
      --                 What we should definitely do is to characterize which of these composition schemes
      --                 corresponds to which implementation, as I tried above.
      --                 Given the extra space in the paper in case of good reviews, we can also shed some light
      --                 on this, and it would also be a great explanation why our implementation of FSTs and
      --                 algebra slightly deviates from the Apel paper + why even in the Apel paper there seem
      --                 to be minor inconsistencies.
      --                 Good job! 🤩
      --
      --             Thinking about it, 3 is way more intuitive than 2 (maybe
      --             even "trivial" 😂).
      --     --> @ibbem: I guess both 1 and 3 are in a sense more intuitive because they just concatenate and
      --                 then eliminate duplicates by favoring either the left or right occurence.
      --                 I am so biased by now, thinking 2 is super intuitive but it probably is not indeed. 😅
      --                 In my mind, the numbers on the left start to walk to the right one by one, starting with the leftmost number.
      --                 I agree though, and we should probably replace the formulation in the paper with 1 or 3.
      --
      --             Currently, I can't think of a simple way to convert 1 or 2
      --             into 3 or 4 without having implementation knowledge.
      --     --> @ibbem: If this way does not exist, it would mean that there exist incompatible algebras right?
      --                 I mean assuming we find an abstract formulation for 3 and 4 in the first place (maybe aab=ab?).
      --             However, for FSTs, mirroring the variant (visually, on the
      --             y-axis) before and after the composition seems to work.
      --             e.g. 3. l ⊕ r = mirror (mergeDuplicatesIntoRightmost (mirror (l ++ r)))
      --             with
      --             mirror fs = map mirror' (reverse fs)
      --             mirror' (a -< cs >-) = a -< mirror cs >-
      --     --> @ibbem: Interesting. This 'mirror function then embodies the flipping _after_ composition.
      --                 So again, we find a commuting square, which tells us that we can "toggle" dominance
      --                 at multiple levels:
      --
      --                                FST² <--- swap ---> FST²
      --                                 |                   |
      --                                 |                   |                Algebra
      --                                _⊕_  <--- flip ---> _⊕_
      --                                 |                   |
      --                                 |                   |           ------------------
      --                                 V                   V
      --                                FST  <-- mirror --> FST            Implementation
      --
      --                                           |
      --                            left-dominant  |  right-dominant
      --                                           |
      --
      --                 So we can toggle dominance not only on the implementation but also the algebra level.
      --                 In the algebra, we can perform 'swap' and 'flip' but not 'mirror'.
      --
      --                 I guess the reason for you not finding a way to toggle from 1/2 to and from 3/4 with just _⊕_ is the following:
      --                 As you have demonstrated above, _⊕_ performs two actions: concatenation _++_ and eliminating duplicates
      --                 (which besides is the reason for the unique-neighbors-axiom).
      --                 So maybe, the algebra needs finer granularity in assuming the existence of both of these operations,
      --                 splitting _⊕_ into the two sub-operations.
      --
      -- This is, duplicates of i have no effect.
      -- ^- TODO ibbem: So this is wrong, right?
      -- @pmbittner: Yes, strictly speaking. I think a better explanation would
      --             be "This is, additional introductions on the right have no
      --             effect."
      -- @ibbem    : Ok, let's rephrase accordingly, once we figured out how to handle
      --             the above ordering thoughts.
      distant-idempotence : ∀ (i₁ i₂ : I) → i₁ ⊕ (i₂ ⊕ i₁) ≡ i₁ ⊕ i₂

      -- The following laws are already stated equivalently above. However, they
      -- serve as a trick to proof that translation between LeftDominant and
      -- RightDominant is a bijection without using the funtion extensionality
      -- or K axiom.
      -- This trick is an adaption of a similar trick used in
      --   https://github.com/agda/agda-categories
      -- as explain in
      --   https://www.youtube.com/live/VQiQtH47pbM?si=AJAI24-dhYypr7p9&t=650
      distant-idempotence' : ∀ (i₁ i₂ : I) → (i₁ ⊕ i₂) ⊕ i₁ ≡ i₁ ⊕ i₂
      associative' : ∀ a b c → (a ⊕ (b ⊕ c)) ≡ ((a ⊕ b) ⊕ c)

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
module RightDominant where
  record FeatureAlgebra {c} (I : Set c) (sum : Op₂ I) (𝟘 : I) : Set (suc c) where
    open Eq.≡-Reasoning

    _⊕_ = sum
    infixr 7 _⊕_

    field
      monoid : IsMonoid _≡_ _⊕_ 𝟘

      -- Only the rightmost occurence of an introduction is effective in a sum,
      -- because it has been introduced first.
      -- This is, duplicates of i have no effect.
      distant-idempotence : ∀ (i₁ i₂ : I) → i₂ ⊕ (i₁ ⊕ i₂) ≡ i₁ ⊕ i₂

      -- See `LeftDominant` for documentation of the following fields.
      distant-idempotence' : ∀ (i₁ i₂ : I) → (i₂ ⊕ i₁) ⊕ i₂ ≡ i₁ ⊕ i₂
      associative' : ∀ a b c → (a ⊕ (b ⊕ c)) ≡ ((a ⊕ b) ⊕ c)

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
  → LeftDominant.FeatureAlgebra I _⊕_ 𝟘
  → RightDominant.FeatureAlgebra I _⊕_ 𝟘
  → Commutative _≡_ _⊕_
commutativity I _⊕_ 𝟘 faˡ faʳ a b =
    a ⊕ b
  ≡⟨ LeftDominant.FeatureAlgebra.distant-idempotence faˡ a b ⟨
    a ⊕ (b ⊕ a)
  ≡⟨ RightDominant.FeatureAlgebra.distant-idempotence faʳ b a ⟩
    b ⊕ a
  ∎
  where
  open Eq.≡-Reasoning

open LeftDominant.FeatureAlgebra
open RightDominant.FeatureAlgebra
open IsMonoid
open IsSemigroup
open IsMagma

left→right : ∀ {c} (I : Set c) (sum : Op₂ I) (𝟘 : I)
  → LeftDominant.FeatureAlgebra I sum 𝟘
  → RightDominant.FeatureAlgebra I (flip sum) 𝟘
left→right I sum 𝟘 faˡ = record
  { monoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = isEquivalence (isMagma (isSemigroup (monoid faˡ)))
        ; ∙-cong = flip (∙-cong (isMagma (isSemigroup (monoid faˡ))))
        }
      ; assoc = λ a b c → associative' faˡ c b a
      }
    ; identity = swap (identity (monoid faˡ))
    }
  ; distant-idempotence = λ a b → distant-idempotence' faˡ b a
  ; distant-idempotence' = λ a b → distant-idempotence faˡ b a
  ; associative' = λ a b c → assoc (isSemigroup (monoid faˡ)) c b a
  }

right→left : ∀ {c} (I : Set c) (sum : Op₂ I) (𝟘 : I)
  → RightDominant.FeatureAlgebra I sum 𝟘
  → LeftDominant.FeatureAlgebra I (flip sum) 𝟘
right→left I sum 𝟘 faʳ = record
  { monoid = record
    { isSemigroup = record
      { isMagma = record
        { isEquivalence = isEquivalence (isMagma (isSemigroup (monoid faʳ)))
        ; ∙-cong = flip (∙-cong (isMagma (isSemigroup (monoid faʳ))))
        }
      ; assoc = λ a b c → associative' faʳ c b a
      }
    ; identity = swap (identity (monoid faʳ))
    }
  ; distant-idempotence = λ a b → distant-idempotence' faʳ b a
  ; distant-idempotence' = λ a b → distant-idempotence faʳ b a
  ; associative' = λ a b c → assoc (isSemigroup (monoid faʳ)) c b a
  }

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
  invˡ {faˡ} x rewrite x = Eq.refl

  invʳ : Inverseʳ _≡_ _≡_ (left→right I (flip sum) 𝟘) (right→left I sum 𝟘)
  invʳ {faʳ} x rewrite x = Eq.refl
