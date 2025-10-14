{-|
This module defines variant types for variability
languages. In particular, we define Rose trees here
as we use in our paper.
-}
module Vatras.Framework.Variants where

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (nothing; just)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.String using (String; _++_; intersperse)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl)
open Eq.≡-Reasoning

open import Function using (id; _∘_; flip)
open import Size using (Size; ↑_; ∞)

open import Vatras.Framework.Definitions using (𝕍; 𝔸; atoms)
open import Vatras.Framework.VariabilityLanguage
open import Vatras.Framework.Compiler using (LanguageCompiler)
open LanguageCompiler

{-|
A rose tree is a tree in which every node stores some data 'A' and
each node has an (unbounded) list of child nodes.
For nodes, we use the artifact syntax from the choice calculus:
a -< es >-
is a node with data 'a : atoms A' and a list of children 'es : List (Rose i A)'.
Rose trees are sized for termination checking.
-}
data Rose : Size → 𝕍 where
  _-<_>- : ∀ {i} {A : 𝔸} → atoms A → List (Rose i A) → Rose (↑ i) A

Forest : 𝕍
Forest A = List (Rose ∞ A)

{-|
Variants for gruler's language also form trees but opposed to rose trees,
nodes are binary and data is stored only in leaves.
This model is slightly simplified from:
_Alexander Gruler. 2010. A Formal Approach to Software Product Families. Ph. D. Dissertation. TU München_
-}
data GrulerVariant : 𝕍 where
  -- the empty variant
  ε     : ∀ {A : 𝔸} → GrulerVariant A
  -- an asset is a leaf node that stores a single data element
  asset : ∀ {A : 𝔸} (a : atoms A) → GrulerVariant A
  -- parallel composition is a node with exactly two children
  _∥_   : ∀ {A : 𝔸} (l : GrulerVariant A) → (r : GrulerVariant A) → GrulerVariant A

-- smart constructor for leaf nodes in rose trees
rose-leaf : ∀ {A : 𝔸} → atoms A → Rose ∞ A
rose-leaf {A} a = a -< [] >-

forest-leaf : ∀ {A : 𝔸} → atoms A → Forest A
forest-leaf a = rose-leaf a ∷ []

forest-singleton : ∀ {A : 𝔸} → atoms A → Forest A → Forest A
forest-singleton a l = a -< l >- ∷ []

{-|
Interestingly, variants are also variability languages
(and it does not matter how variants actually look like).
When variants are expressions, we can just not configure anything
to obtain an expression.
As a configuration language, we can just use ⊤ because the only
requirement we have is that there must be at least one configuration
but it is irrelevant what it is.
-}
Variant-is-VL : ∀ (V : 𝕍) → VariabilityLanguage V
Variant-is-VL V = ⟪ V , ⊤ , (λ e _ → e) ⟫

GrulerVL : VariabilityLanguage GrulerVariant
GrulerVL = Variant-is-VL GrulerVariant

RoseVL : VariabilityLanguage (Rose ∞)
RoseVL = Variant-is-VL (Rose ∞)

{-|
Lemma to conclude that the child lists of two equal rose trees must be equal as well.
-}
children-equality : ∀ {A : 𝔸} {a₁ a₂ : atoms A} {cs₁ cs₂ : List (Rose ∞ A)} → a₁ -< cs₁ >- ≡ a₂ -< cs₂ >- → cs₁ ≡ cs₂
children-equality refl = refl

{-|
Show function for rose trees.
-}
show-rose : ∀ {i} {A} → (atoms A → String) → Rose i A → String
show-rose show-a (a -< [] >-)         = show-a a
show-rose show-a (a -< es@(_ ∷ _) >-) = show-a a ++ "-<" ++ (intersperse ", " (map (show-rose show-a) es)) ++ ">-"

{-|
A variant encoder embeds variants into variability languages.
Variability languages denote sets of variants.
Hence, they must be able to somehow describe variants in some way.
This means that often, variants can be encoded directly into a variability language.
The result is an expression which cannot be configured
(i.e., configurations don't matter because there is only
a single variant anyway).
To define variant encoders, we can just reuse our definition for compilers
and then define an encoder to be a compiler from variants to a particular language
-}
VariantEncoder : ∀ (V : 𝕍) (L : VariabilityLanguage V) → Set₁
VariantEncoder V L = LanguageCompiler (Variant-is-VL V) L

{-|
This module groups some interesting properties of variant encoders.
-}
module _ (V : 𝕍) (A : 𝔸) {L : VariabilityLanguage V} (encoder : VariantEncoder V L) where
  open import Vatras.Data.EqIndexedSet

  private
    ⟦_⟧ = Semantics L
    ⟦_⟧ᵥ = Semantics (Variant-is-VL V)

  {-|
  The semantics of an encoded variant is a singleton indexed set.
  This means that encoding a variant produces an expression that describes
  exactly one variant.
  -}
  encoded-variant-is-singleton-set :
    ∀ (v : V A) → Singleton ⟦ compile encoder v ⟧
  encoded-variant-is-singleton-set v = v , λ c → proj₂ (preserves encoder v) c

  {-|
  Correctness criterion of variant encoders:
  Encoding a variant and configuring the resulting expression
  always yields back the initial variant.
  This is desired because we want to encode exactly the given
  variant (nothing more, nothing less).
  -}
  encode-idemp : ∀ (c : Config L) (v : V A)
    → ⟦ compile encoder v ⟧ c ≡ v
  encode-idemp c v =
    begin
      ⟦ compile encoder v ⟧ c
    ≡⟨ irrelevant-index (encoded-variant-is-singleton-set v) ⟩
      ⟦ compile encoder v ⟧ (conf encoder v tt)
    ≡⟨ proj₁ (preserves encoder v) tt ⟨
      ⟦ v ⟧ᵥ tt
    ≡⟨⟩
      v
    ∎

-- atom containment
open import Relation.Nullary.Decidable using (yes; no)
open import Data.Bool using (Bool; true)
open import Data.Bool.ListAction using (or)

has-atom : ∀ {A i} → atoms A → Rose i A → Bool
has-atom {A , _≟_} a (b -< cs >-) with a ≟ b
... | yes refl = true
... | no x = or (map (has-atom b) cs)
