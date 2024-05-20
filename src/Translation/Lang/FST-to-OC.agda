open import Framework.Definitions using (𝔽; 𝔸; atoms)
open import Relation.Binary using (DecidableEquality)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_; refl)

module Translation.Lang.FST-to-OC {F : 𝔽} (f₁ f₂ : F) (f₁≢f₂ : f₁ ≢ f₂) (_==ꟳ_ : DecidableEquality F) where

open import Size using (∞)
open import Data.Bool as Bool using (true; false)
import Data.Bool.Properties as Bool
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List as List using (List; []; _∷_; length; catMaybes)
open import Data.List.Properties as List
open import Data.List.Relation.Binary.Sublist.Heterogeneous using ([]; _∷_; _∷ʳ_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (zero; suc; _≟_; ℕ; _+_; _≤_; z≤n; s≤s)
import Data.Nat.Properties as ℕ
open import Data.Product using (_,_; ∃-syntax)
open import Data.Sum as Sum using (_⊎_; inj₁; inj₂)
open import Function using (flip)
open import Relation.Nullary using (yes; no)

open Eq.≡-Reasoning

open import Framework.Variants using (Rose; rose-leaf; _-<_>-; children-equality)
import Construct.Plain.Artifact
open import Lang.All
open OC using (WFOCL; Root; _❲_❳; all-oc)
open import Lang.OC.Properties using (⟦e⟧ₒtrue≡just)
open import Lang.OC.Subtree using (Subtree; subtrees; both; neither; Implies; subtreeₒ; subtreeₒ-recurse)
open import Lang.FST using (FSTL-Sem)
open FST using (FSTL)
open FST.Impose

V = Rose ∞
open import Framework.Relation.Expressiveness V using (_⋡_)

A : 𝔸
A = ℕ , _≟_

-- This represents a form of an alternative where there are the variants
--   zero -< zero -<     zero -< [] >- ∷ [] >- ∷ [] >-
--   zero -< zero -< suc zero -< [] >- ∷ [] >- ∷ [] >-
-- but there is no
--   zero -< zero -<                     [] >- ∷ [] >-
-- variant. Hence, at least one inner children is required. Note, however, that
-- there are two more variants:
--   zero -< zero -< zero -< [] >- ∷ suc zero -< [] >- ∷ [] >- ∷ [] >-
--   zero -<                                                >- ∷ [] >-
--
-- The idea of the following proof is to show that any OC expression will
-- necessarily have to include some other variant.
-- We identified two cases:
--
-- - The `shared-artifact` case includes the extra variant
--     zero -< zero -<                     [] >- ∷ [] >-
--   For example:
--     zero -< zero -< f₁ ❲ zero -< [] >- ❳ ∷ f₂ ❲ suc zero -< [] >- ❳ ∷ [] >- ∷ [] >-
--
-- - The `more-artifacts` case includes an extra variant like
--     zero -< zero -< zero -< [] >- ∷ [] >- ∷ zero -< suc zero -< [] >- ∷ [] >- ∷ [] >-
--   for example
--     zero -< f₁ ❲ zero -< zero -< [] >- ∷ [] >- ❳ ∷ f₂ ❲ zero -< suc zero -< [] >- ∷ [] >- ❳ ∷ [] >-
--   Note that, in contrast to the `shared-artifact` case, this variant is
--   not uniquely determined. In fact, The order of the two features isn't fixed
--   and the configuration chosen by the proof could introduce more artifacts
--   because there can be options which are not selected by the configurations
--   `c₁` and `c₂` below.
counter-example : SPL F A
counter-example = zero ◀ (
    (f₁ :: ((zero -<     zero -< [] >- ∷ [] >- ∷ []) ⊚ ([] ∷ [] , (([] ∷ []) , (([] , []) ∷ [])) ∷ [])))
  ∷ (f₂ :: ((zero -< suc zero -< [] >- ∷ [] >- ∷ []) ⊚ ([] ∷ [] , (([] ∷ []) , (([] , []) ∷ [])) ∷ [])))
  ∷ [])

-- There are four relevant configurations for `counter-example` because it uses
-- exactly two features: `c₁`, `c₂`, `all-oc true` and `all-oc false`.
c₁ : FST.Configuration F
c₁ f with f ==ꟳ f₁
c₁ f | yes f≡f₁ = true
c₁ f | no f≢f₁ = false

c₂ : FST.Configuration F
c₂ f with f ==ꟳ f₂
c₂ f | yes f≡f₂ = true
c₂ f | no f≢f₂ = false

-- To be as general as possible, we do not fix `F` but only require that it
-- contains at least two different features `f₁` and `f₂`. To implement `c₁` and
-- `c₂` equality in `F` nees to be decidable, so `==ꟳ` is also required.
-- However, Agda can't compute with `==ꟳ` so we need the following two lemmas to
-- sort out invalid definitions of `==ꟳ` and actually compute the semantics of
-- `counter-example`.
compute-counter-example-c₁ : {a : Rose ∞ A} → FSTL-Sem F counter-example c₁ ≡ a → zero -< zero -< zero -< [] >- ∷ [] >- ∷ [] >- ≡ a
compute-counter-example-c₁ p with f₁ ==ꟳ f₁ | f₂ ==ꟳ f₁ | c₁ f₁ in c₁-f₁ | c₁ f₂ in c₁-f₂
compute-counter-example-c₁ p | yes f₁≡f₁ | yes f₂≡f₁ | _ | _ = ⊥-elim (f₁≢f₂ (Eq.sym f₂≡f₁))
compute-counter-example-c₁ p | yes f₁≡f₁ | no f₂≢f₁ | true | false = p
compute-counter-example-c₁ p | no f₁≢f₁ | _ | _ | _ = ⊥-elim (f₁≢f₁ refl)

compute-counter-example-c₂ : {a : Rose ∞ A} → FSTL-Sem F counter-example c₂ ≡ a → zero -< zero -< suc zero -< [] >- ∷ [] >- ∷ [] >- ≡ a
compute-counter-example-c₂ p with f₁ ==ꟳ f₂ | f₂ ==ꟳ f₂ | c₂ f₁ in c₂-f₁ | c₂ f₂ in c₂-f₂
compute-counter-example-c₂ p | yes f₁≡f₂ | _ | _ | _ = ⊥-elim (f₁≢f₂ f₁≡f₂)
compute-counter-example-c₂ p | no f₁≢f₂ | yes f₂≡f₂ | false | true = p
compute-counter-example-c₂ p | no f₁≢f₂ | no f₂≢f₂ | _ | _ = ⊥-elim (f₂≢f₂ refl)

-- For proving the `shared-artifact` case, we need to compute a configuration
-- which deselects the options guarding the inner artifacts (`zero -< [] >-` and
-- `suc zero -< [] >-`) but selects all options leading to the shared artifact
-- surrounding these two options.
_∧_ : {F : 𝔽} → OC.Configuration F → OC.Configuration F → OC.Configuration F
_∧_ c₁ c₂ f = c₁ f Bool.∧ c₂ f

implies-∧₁ : {F : 𝔽} {c₁ c₂ : OC.Configuration F} → Implies (c₁ ∧ c₂) c₁
implies-∧₁ {c₁ = c₁} f p with c₁ f
implies-∧₁ f p | true = refl

implies-∧₂ : {F : 𝔽} {c₁ c₂ : OC.Configuration F} → Implies (c₁ ∧ c₂) c₂
implies-∧₂ {c₁ = c₁} {c₂ = c₂} f p with c₁ f | c₂ f
implies-∧₂ f p | true | true = refl

-- In case we found a node corresponding to either `zero -< zero -< [] >- ∷ [] >-`
-- or `zero -< suc zero -< [] >- ∷ [] >-`, we choose the all true configuration
-- and proof that there is at least one more artifact in the resulting variant.
--
-- As discussed at the definition of `counter-example`, the order of the
-- artifact nodes is not uniquely determined. Hence, there are two distinct
-- cases in `induction`, which we abstract over using the `v` argument.
-- Moreover, we only prove that there is one more artifact in the variant.  In
-- addition, there can be additional options, only present in the all true
-- configuration, which is why we only prove that there is at least one more
-- artifact.
more-artifacts : ∀ {F' : 𝔽}
  → (cs : List (OC.OC F' ∞ A))
  → (cₙ : OC.Configuration F')
  → (v : Rose ∞ A)
  → zero -< v ∷ [] >- ∷ [] ≡ OC.⟦ cs ⟧ₒ-recurse cₙ
  → 1 ≤ length (OC.⟦ cs ⟧ₒ-recurse (all-oc true))
more-artifacts (a OC.-< cs' >- ∷ cs) cₙ v p = s≤s z≤n
more-artifacts (e@(f OC.❲ e' ❳) ∷ cs) cₙ v p with OC.⟦ e ⟧ₒ (all-oc true) | ⟦e⟧ₒtrue≡just e
more-artifacts (e@(f OC.❲ e' ❳) ∷ cs) cₙ v p | .(just _) | _ , refl = s≤s z≤n

-- In this case, the relevant options are contained in the same, shared, option
-- `e`.  The goal is to proof that we can deselect all inner options and obtain
-- this shared artifact without any inner artifacts.
--
-- As configuration, we chose the intersection of the two given configurations.
-- This ensures that all options up to the shared artifact are included because
-- they must be included in both variants. Simultaneously, this excludes the
-- artifacts themselves because each configuration excludes one of them.
shared-artifact : ∀ {F' : 𝔽}
  → (e : OC.OC F' ∞ A)
  → (c₁ c₂ : OC.Configuration F')
  → just (zero -< rose-leaf      zero  ∷ [] >-) ≡ OC.⟦ e ⟧ₒ c₁
  → just (zero -< rose-leaf (suc zero) ∷ [] >-) ≡ OC.⟦ e ⟧ₒ c₂
  → just (zero -< [] >-) ≡ OC.⟦ e ⟧ₒ (c₁ ∧ c₂)
shared-artifact (zero OC.-< cs >-) c₁ c₂ p₁ p₂ with OC.⟦ cs ⟧ₒ-recurse c₁ | OC.⟦ cs ⟧ₒ-recurse c₂ | OC.⟦ cs ⟧ₒ-recurse (c₁ ∧ c₂) | subtreeₒ-recurse cs (c₁ ∧ c₂) c₁ implies-∧₁ | subtreeₒ-recurse cs (c₁ ∧ c₂) c₂ (implies-∧₂ {c₁ = c₁})
shared-artifact (zero OC.-< cs >-) c₁ c₂ refl refl | _ | _ | [] | _ | _ = refl
shared-artifact (zero OC.-< cs >-) c₁ c₂ refl refl | _ | _ | _ ∷ _ | subtrees _ ∷ _ | () ∷ _
shared-artifact (f OC.❲ e ❳) c₁ c₂ p₁ p₂ with c₁ f | c₂ f
shared-artifact (f OC.❲ e ❳) c₁ c₂ p₁ p₂ | true | true = shared-artifact e c₁ c₂ p₁ p₂

-- This is the main induction over the top most children of the OC expression.
-- It requires two configuration which evaluate to the two alternative variants.
-- For simplicity, though not actually required for the result, it also takes a
-- configuration showing that the semantics of the expression includes a variant
-- without children. This eliminates a bunch of proof cases (e.g. having an
-- unconditional artifact).
--
-- The idea is to find a child which exists in at least one of the variants
-- configured by `c₁` or `c₂`. Hence, we do a case analysis on whether a given
-- option exists when evaluated with the configurations `c₁` and `c₂` (we can
-- ignore artifacts because of `c₃`). Note that evaluating the configuration for
-- this option alone is not enough to guarantee that there is an artifact
-- because options can be nested arbitrarily deep without artifacts in between.
--
-- If an option evaluates to an artifact in exactly one of the configurations,
-- we know there must be a second option in `cs` evaluating to the an artifact
-- in the other configuration. In this case, called `more-artifacts`, we count
-- the top level child artifacts when the OC expression is evaluated using the
-- all true configuration.
--
-- If an option evaluates to an artifact for both `c₁` and `c₂` it must also
-- evaluate to an artifact for the intersection of these configurations. The
-- resulting variant can't include the child artifacts of the `c₁` and `c₂`
-- variants forcing it to have exactly one shape. In this case, called
-- `shared-artifact`, we return the exact variant to which the expression
-- evaluates under the intersection of `c₁` and `c₂`.
induction : ∀ {F' : 𝔽}
  → (cs : List (OC.OC F' ∞ A))
  → (c₁ c₂ c₃ : OC.Configuration F')
  → zero -< rose-leaf      zero  ∷ [] >- ∷ [] ≡ OC.⟦ cs ⟧ₒ-recurse c₁
  → zero -< rose-leaf (suc zero) ∷ [] >- ∷ [] ≡ OC.⟦ cs ⟧ₒ-recurse c₂
  → [] ≡ OC.⟦ cs ⟧ₒ-recurse c₃
  → 2 ≤ length (OC.⟦ cs ⟧ₒ-recurse (all-oc true))
  ⊎ zero -< [] >- ∷ [] ≡ OC.⟦ cs ⟧ₒ-recurse (c₁ ∧ c₂)
induction (_ OC.-< _ >- ∷ cs) c₁ c₂ c₃ p₁ p₂ ()
induction (e@(_ OC.❲ _ ❳) ∷ cs) c₁ c₂ c₃ p₁ p₂ p₃ with OC.⟦ e ⟧ₒ c₁ in ⟦e⟧c₁ | OC.⟦ e ⟧ₒ c₂ in ⟦e⟧c₂ | OC.⟦ e ⟧ₒ c₃
induction (e@(_ OC.❲ _ ❳) ∷ cs) c₁ c₂ c₃ p₁ p₂ p₃ | nothing | nothing | nothing with induction cs c₁ c₂ c₃ p₁ p₂ p₃
induction (e@(_ OC.❲ _ ❳) ∷ cs) c₁ c₂ c₃ p₁ p₂ p₃ | nothing | nothing | nothing | inj₁ p with OC.⟦ e ⟧ₒ (all-oc true)
induction (e@(_ OC.❲ _ ❳) ∷ cs) c₁ c₂ c₃ p₁ p₂ p₃ | nothing | nothing | nothing | inj₁ p | just _ = inj₁ (ℕ.≤-trans p (ℕ.n≤1+n _))
induction (e@(_ OC.❲ _ ❳) ∷ cs) c₁ c₂ c₃ p₁ p₂ p₃ | nothing | nothing | nothing | inj₁ p | nothing = inj₁ p
induction (e@(_ OC.❲ _ ❳) ∷ cs) c₁ c₂ c₃ p₁ p₂ p₃ | nothing | nothing | nothing | inj₂ p with OC.⟦ e ⟧ₒ (c₁ ∧ c₂) | OC.⟦ e ⟧ₒ c₁ | subtreeₒ e (c₁ ∧ c₂) c₁ implies-∧₁
induction (e@(_ OC.❲ _ ❳) ∷ cs) c₁ c₂ c₃ p₁ p₂ p₃ | nothing | nothing | nothing | inj₂ p | nothing | nothing | neither = inj₂ p
induction (e@(_ OC.❲ _ ❳) ∷ cs) c₁ c₂ c₃ p₁ p₂ p₃ | nothing | just _  | nothing with OC.⟦ e ⟧ₒ c₂ | ⟦e⟧c₂ | OC.⟦ e ⟧ₒ (all-oc true) | subtreeₒ e c₂ (all-oc true) (λ f p → refl)
induction (e@(_ OC.❲ _ ❳) ∷ cs) c₁ c₂ c₃ p₁ p₂ p₃ | nothing | just _  | nothing | just _ | _ | .(just _) | both _ = inj₁ (s≤s (more-artifacts cs c₁ (rose-leaf zero) p₁))
induction (e@(_ OC.❲ _ ❳) ∷ cs) c₁ c₂ c₃ p₁ p₂ p₃ | just _  | nothing | nothing with OC.⟦ e ⟧ₒ c₁ | ⟦e⟧c₁ | OC.⟦ e ⟧ₒ (all-oc true) | subtreeₒ e c₁ (all-oc true) (λ f p → refl)
induction (e@(_ OC.❲ _ ❳) ∷ cs) c₁ c₂ c₃ p₁ p₂ p₃ | just _  | nothing | nothing | just _ | _ | .(just _) | both _ = inj₁ (s≤s (more-artifacts cs c₂ (rose-leaf (suc zero)) p₂))
induction (e@(_ OC.❲ _ ❳) ∷ cs) c₁ c₂ c₃ p₁ p₂ p₃ | just _  | just _  | nothing with List.∷-injectiveʳ p₁
induction (e@(_ OC.❲ _ ❳) ∷ cs) c₁ c₂ c₃ p₁ p₂ p₃ | just _  | just _  | nothing | _ with OC.⟦ cs ⟧ₒ-recurse (c₁ ∧ c₂) in ⟦cs⟧c₁∧c₂ | OC.⟦ cs ⟧ₒ-recurse c₁ | subtreeₒ-recurse cs (c₁ ∧ c₂) c₁ implies-∧₁
induction (e@(_ OC.❲ _ ❳) ∷ cs) c₁ c₂ c₃ p₁ p₂ p₃ | just _  | just _  | nothing | _ | .[] | .[] | [] = inj₂ (
    zero -< [] >- ∷ []
  ≡⟨ Eq.cong₂ _∷_ refl ⟦cs⟧c₁∧c₂ ⟨
    zero -< [] >- ∷ OC.⟦ cs ⟧ₒ-recurse (c₁ ∧ c₂)
  ≡⟨⟩
    catMaybes (just (zero -< [] >-) ∷ List.map (flip OC.⟦_⟧ₒ (c₁ ∧ c₂)) cs)
  ≡⟨ Eq.cong catMaybes (Eq.cong₂ _∷_ (shared-artifact e c₁ c₂
                                                      (Eq.trans (Eq.cong just (List.∷-injectiveˡ p₁)) (Eq.sym ⟦e⟧c₁))
                                                      (Eq.trans (Eq.cong just (List.∷-injectiveˡ p₂)) (Eq.sym ⟦e⟧c₂)))
                                      refl) ⟩
    catMaybes (OC.⟦ e ⟧ₒ (c₁ ∧ c₂) ∷ List.map (flip OC.⟦_⟧ₒ (c₁ ∧ c₂)) cs)
  ≡⟨⟩
    OC.⟦ e ∷ cs ⟧ₒ-recurse (c₁ ∧ c₂)
  ∎)

-- The results of the `induction` show that OC has no equivalent to the FST
-- expression. The proof evaluates the FST expression on all relevant
-- configurations which results in contradictions in every case.
impossible : ∀ {F' : 𝔽}
  → (cs : List (OC.OC F' ∞ A))
  → (c₁ c₂ : OC.Configuration F')
  → ((c : OC.Configuration F') → ∃[ c' ] OC.⟦ Root zero cs ⟧ c ≡ FSTL-Sem F counter-example c')
  → 2 ≤ length (OC.⟦ cs ⟧ₒ-recurse (all-oc true))
  ⊎ zero -< [] >- ∷ [] ≡ OC.⟦ cs ⟧ₒ-recurse (c₁ ∧ c₂)
  → ⊥
impossible cs c₁ c₂ alternative⊆e (inj₁ p) with alternative⊆e (all-oc true)
impossible cs c₁ c₂ alternative⊆e (inj₁ p) | c' , e' with OC.⟦ cs ⟧ₒ-recurse (all-oc true) | c' f₁ | c' f₂
impossible cs c₁ c₂ alternative⊆e (inj₁ (s≤s ())) | c' , e' | _ ∷ [] | _ | _
impossible cs c₁ c₂ alternative⊆e (inj₁ p) | c' , () | _ ∷ _ ∷ _ | false | false
impossible cs c₁ c₂ alternative⊆e (inj₁ p) | c' , () | _ ∷ _ ∷ _ | false | true
impossible cs c₁ c₂ alternative⊆e (inj₁ p) | c' , () | _ ∷ _ ∷ _ | true  | false
impossible cs c₁ c₂ alternative⊆e (inj₁ p) | c' , () | _ ∷ _ ∷ _ | true  | true
impossible cs c₁ c₂ alternative⊆e (inj₂ p) with alternative⊆e (c₁ ∧ c₂)
impossible cs c₁ c₂ alternative⊆e (inj₂ p) | c' , e' with c' f₁ | c' f₂ | Eq.trans (Eq.cong (zero -<_>-) p) e'
impossible cs c₁ c₂ alternative⊆e (inj₂ p) | c' , e' | false | false | ()
impossible cs c₁ c₂ alternative⊆e (inj₂ p) | c' , e' | false | true  | ()
impossible cs c₁ c₂ alternative⊆e (inj₂ p) | c' , e' | true  | false | ()
impossible cs c₁ c₂ alternative⊆e (inj₂ p) | c' , e' | true  | true  | ()

-- With a little plumbing we can now conclude that there are Feature Structure
-- Trees (FST) with no Option Calculus (OC) equivalent.
WFOCL⋡FSTL : ∀ {F' : 𝔽} → WFOCL F' ⋡ FSTL F
WFOCL⋡FSTL WFOCL≽FSTL with WFOCL≽FSTL counter-example
WFOCL⋡FSTL WFOCL≽FSTL | Root a cs , e⊆alternative , alternative⊆e with e⊆alternative c₁ | e⊆alternative c₂ | e⊆alternative (all-oc false)
WFOCL⋡FSTL {F'} WFOCL≽FSTL | Root zero cs , e⊆alternative , alternative⊆e | (c₁ , p₁) | (c₂ , p₂) | (c₃ , p₃) =
  impossible cs c₁ c₂ alternative⊆e
    (induction cs c₁ c₂ c₃ (children-equality (compute-counter-example-c₁ p₁))
                           (children-equality (compute-counter-example-c₂ p₂))
                           (children-equality p₃))
