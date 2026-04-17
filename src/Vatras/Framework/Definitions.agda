module Vatras.Framework.Definitions where

open import Data.Maybe using (Maybe; just)
open import Data.Nat as ℕ using (ℕ; zero)
open import Data.Product using (_×_; Σ; Σ-syntax; proj₁; proj₂) renaming (_,_ to _and_)
import Data.Product.Properties as Product
open import Data.String as String using (String)
open import Data.Unit using (⊤; tt) public
open import Function using (id; _∘_; const)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl)
open import Relation.Binary using (DecidableEquality)
open import Relation.Nullary.Negation using (¬_)

{-|
Some Atomic Data.
Any type can be used as atomic data in variants as long as
we can decide equality.
Our framework as well as most variability language actually
do not require decidable equality but a few variability languages
require it (e.g., feature structure trees).
We decided to include the assumption that equality is decidable into
the core definitions because it is quite reasonable.
Any actual data we can think of to plug in here (e.g., strings, tokens or
nodes of an abstract syntax tree) can be checked for equality.
-}
record 𝔸 : Set₁ where
  -- We do not actually need eta equality in Vatras and it does break a proof when enabled (no idea why).
  no-eta-equality
  field
    atoms : Set
    atomsEqual? : DecidableEquality atoms
    atomSize : atoms → ℕ
open 𝔸 public

{-|
Variant Language.
A variant should represent atomic data in some way so its parameterized in atomic data.
In our paper, this type is fixed to rose trees (see Vatras.Framework.Variants.agda).
-}
𝕍 : Set₂
𝕍 = 𝔸 → Set₁

{-|
Annotation Language.
This can be names or propositional formulas or whatever you like to annotate artifacts with.
We have no assumptions on this kind of language (yet).
In the future, it might be interesting to dig deeper into 𝔽 and to explore its impact on a
language's expressiveness more deeply.
-}
𝔽 : Set₁
𝔽 = Set

{-|
Configuration Languages.
We have no assumptions on this kind of language (yet).
-}
ℂ : Set₁
ℂ = Set

{-|
Syntax of variability languages.
An instance of 𝔼 denotes set of expressions of a variability language.
An expression denotes a set of variants and hence, variant-like sub-terms occur within an expression.
Such sub-terms describe variants of atomic data (i.e., some structure on atomic elements),
and hence expressions are parameterized in the type of this atomic data.
-}
𝔼 : Set₂
𝔼 = 𝔸 → Set₁

-- some default atoms
{-|
String artifacts.
Equality is defined character wise
and size is measured by length (in characters not bytes).
-}
STRING : 𝔸
STRING = record
  { atoms = String
  ; atomsEqual? = String._≟_
  ; atomSize = String.length
  }

{-|
Pairs of natural numbers as artifacts.
The first element in the pair is treated as an identifier
whereas the second element determines the size of the artifact.
Both elements of the pair are tested for equality.
-}
NAT : 𝔸
NAT = record
  { atoms = ℕ × ℕ
  ; atomsEqual? = Product.≡-dec ℕ._≟_ ℕ._≟_
  ; atomSize = proj₂
  }

{-|
Natural number artifacts.
Each number is treated as a separate artifact.
The size of all artifacts is zero.
-}
NAT' : 𝔸
NAT' = record
  { atoms = ℕ
  ; atomsEqual? = ℕ._≟_
  ; atomSize = const zero
  }
