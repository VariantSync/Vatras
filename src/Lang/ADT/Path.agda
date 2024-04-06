open import Framework.Definitions using (𝔽; 𝕍; 𝔸; 𝔼)
open import Relation.Binary using (DecidableEquality; Rel)
module Lang.ADT.Path
  (F : 𝔽)
  (V : 𝕍)
  (_==_ : DecidableEquality F)
  where

open import Level using (0ℓ)
open import Function using (_∘_)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (Any; here; there)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (¬Any⇒All¬)
open import Data.List.Relation.Unary.AllPairs using (AllPairs; []; _∷_)
open import Data.Product using (_×_; ∃-syntax)

open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (yes; no; False; True; isYes; fromWitness; toWitness; fromWitnessFalse; toWitnessFalse)
open import Relation.Binary using (Decidable; Symmetric)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym)
open Eq.≡-Reasoning

open import Framework.VariabilityLanguage
open import Util.Suffix using (_endswith_)
open import Lang.ADT using (ADT; leaf; _⟨_,_⟩; Configuration; ⟦_⟧)

-- A selection of a feature matches it to a boolean value.
record Selection : Set where
  constructor _↣_
  field
    feature : F
    value : Bool
open Selection public

-- A list of selection which denotes a path from the root of a ADT to a leaf node.
Path : Set
Path = List Selection

-- Two Selections are considered different iff they have different features.
-- Notable, (A ↣ true) is not different to (A ↣ false).
different : Rel Selection 0ℓ
different (A ↣ _) (B ↣ _) = False (A == B)

sym-different : Symmetric different
sym-different neq = fromWitnessFalse λ eq → toWitnessFalse neq (sym eq)

-- Two selections are considered the same of they assign the same feature.
same : Rel Selection 0ℓ
same (A ↣ _) (B ↣ _) = True (A == B)

-- Checks whether a given features was assigned in a selection.
is : F → Selection → Set
is A (B ↣ _) = True (A == B)

is-refl : ∀ (D : F) → (b : Bool) → is D (D ↣ b)
is-refl _ _ = fromWitness refl

==-isYes-refl : ∀ (D : F) → isYes (D == D) ≡ true
==-isYes-refl D with D == D
... | yes refl = refl
... | no D≠D = ⊥-elim (D≠D refl)

-- Checks whether a feature is assigned somewhere in a path.
_∈_ : F → Path → Set
a ∈ as = Any (is a) as

_∉_ : F → Path → Set
D ∉ fs = ¬ (D ∈ fs)

∉-head : ∀ {D x xs} → D ∉ (x ∷ xs) → (b : Bool) → different x (D ↣ b)
∉-head D∉x∷xs b = fromWitnessFalse λ x≡D → D∉x∷xs (here (fromWitness (sym x≡D)))

∉-tail : ∀ {D x xs} → D ∉ (x ∷ xs) → D ∉ xs
∉-tail D∉x∷xs D∈xs = D∉x∷xs (there D∈xs)

-- Finds the assigned value of a feature within a path.
getValue : ∀ {a fs} → a ∈ fs → Bool
getValue (here {_ ↣ value} _) = value
getValue (there fs) = getValue fs

-- Containment _∈_ is decidable.
_∈?_ : Decidable _∈_
a ∈? [] = no λ ()
a ∈? ((x ↣ v) ∷ xs) with a == x
... | yes p = yes (here (fromWitness p))
... | no ¬p with a ∈? xs
...   | yes q = yes (there q)
...   | no ¬q = no nope
  where
    nope : ¬ Any (is a) ((x ↣ v) ∷ xs)
    nope (here  p) = ¬p (toWitness p)
    nope (there q) = ¬q q

-- Turns an ¬ Any to a All ¬.
-- TODO: Reuse ¬Any⇒All¬ from the standard library.
∉→All-different : ∀ {D} → (as : Path) → D ∉ as → All (different (D ↣ true)) as
∉→All-different [] _ = []
∉→All-different (a ∷ as) nope =
    fromWitnessFalse (λ x → nope (here (fromWitness x)))
  ∷ ∉→All-different as λ x → nope (there x)

All-different→∉ : ∀ {D} (b : Bool) (as : Path) → All (different (D ↣ b)) as → D ∉ as
All-different→∉ b (a ∷ as) (pa ∷ pas) (here D-is-a) = toWitnessFalse pa (toWitness D-is-a)
All-different→∉ b (a ∷ as) (pa ∷ pas) (there D∈as)  = All-different→∉ b as pas D∈as

{-
All features mentioned in the path are unique (i.e., no feature is mentioned more than once).
This means that there cannot be conflicts in the path.
-}
Unique : Path → Set
Unique = AllPairs different

{-
A path is starts at a node if it leads to a leaf.
This relation can be seen as a type system for paths within a particular tree.
Note: The symmetry between the rules walk-left and walk-right causes many
      proofs to have quite some redundancy as well because we have to match
      on these rules a lot.
      However, we cannot merge the rules into a single rule
      because we have to recurse on either the left or right alternative (not both).
-}
data _starts-at_ : ∀ {A} → (p : Path) → (e : ADT V F A) → Set where
  tleaf : ∀ {A} {v : V A}
      ------------------
    → [] starts-at (leaf v)

  walk-left : ∀ {A} {D : F} {l r : ADT V F A} {pl : Path}
    → pl starts-at l
      -------------------------------------
    → ((D ↣ true) ∷ pl) starts-at (D ⟨ l , r ⟩)

  walk-right : ∀ {A} {D : F} {l r : ADT V F A} {pr : Path}
    → pr starts-at r
      --------------------------------------
    → ((D ↣ false) ∷ pr) starts-at (D ⟨ l , r ⟩)

{-
An expression does not contain a feature name
if all paths do not contain that feature name.
-}
_∉'_ : ∀{A} → F → ADT V F A → Set
D ∉' e = ∀ (p : Path) → p starts-at e → D ∉ p

{-
A path serves as a configuration for an expression e
if it starts at that expression and ends at a leaf.
-}
record PathConfig {A} (e : ADT V F A) : Set where
  constructor _is-valid_
  field
    path : Path
    valid : path starts-at e
open PathConfig public

{-
Alternative semantics of ADTs by walking a path.
This walk may be illegal by choosing different alternatives for the same choice within a path.
For example in D ⟨ D ⟨ 1 , dead ⟩ , 2 ⟩ we can reach 'dead' via (D ↣ true ∷ D ↣ false ∷ []).
However, walking like this is fine as long as the path is unique as we will later prove.
-}
walk : ∀ {A} → (e : ADT V F A) → PathConfig e → V A
walk (leaf v) ([] is-valid tleaf) = v
walk (D ⟨ l , _ ⟩) ((.(D ↣ true ) ∷ pl) is-valid walk-left  t) = walk l (pl is-valid t)
walk (D ⟨ _ , r ⟩) ((.(D ↣ false) ∷ pr) is-valid walk-right t) = walk r (pr is-valid t)

{-
An expression a is a sub-expression of b
iff all valid paths from a lead to paths from b.
-}
_subexprof_ : ∀ {A} → ADT V F A → ADT V F A → Set
a subexprof b = ∀ (pa : Path) → pa starts-at a → ∃[ pb ] ((pb starts-at b) × (pb endswith pa))

{-
A configuration matches a selection
if the configuration returns the same
result for the given feature as dictated
by the selection.
-}
matches : Configuration F → Selection → Set
matches c (f ↣ val) = c f ≡ val

{-
Predicate that tells whether a path matches a configuration.
This essentially makes the given path a partial configuration.
-}
_⊑_ : Path → Configuration F → Set
p ⊑ c = All (matches c) p

{-
If we make a lookup in a path for a certain feature,
any matching configuration will yield the same result.
-}
lookup-partial : ∀ {p} {c} {D}
  → p ⊑ c
  → (has : D ∈ p)
  → getValue has ≡ c D
lookup-partial (refl ∷ px) (here D-is-f) rewrite toWitness D-is-f = refl
lookup-partial (refl ∷ px) (there has) = lookup-partial px has

