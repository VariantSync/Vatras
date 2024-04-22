# Relating Option Calculus to Binary Choice Calculus

## Options

```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

## Module

```agda
open import Framework.Definitions
open import Framework.Construct
open import Construct.Artifact as At using () renaming (Syntax to Artifact; Construct to Artifact-Construct)
module Translation.Lang.OC-to-2CC (F : 𝔽) where

open import Framework.Variants using (Rose; rose; Artifact∈ₛRose)
open import Size using (Size; ↑_; _⊔ˢ_; ∞)
V = Rose ∞
mkArtifact = Artifact∈ₛRose
Option = F
```

## Imports

```agda
open import Data.Bool using (if_then_else_; true; false)
open import Data.List using (List; _∷_; []; _∷ʳ_; _++_; length; map; catMaybes)
open import Data.Nat using (ℕ)
open import Data.Product using (∃; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_; toList; fromList)
open import Function using (id; _∘_; flip)

open import Framework.VariabilityLanguage
open import Lang.All.Generic V mkArtifact
open OC renaming (_-<_>- to Artifactₒ)
open 2CC renaming (_-<_>- to Artifact₂; ⟦_⟧ to ⟦_⟧₂)

open import Data.EqIndexedSet

Artifactᵥ : ∀ {A} → atoms A → List (Rose ∞ A) → Rose ∞ A
Artifactᵥ a cs = rose (a At.-< cs >-)

open import Util.AuxProofs using (id≗toList∘fromList)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym)
open Eq.≡-Reasoning
```

## Intermediate Language

For the translation of options, we have to remember translated children within the subtree we are currently translating.
Therefore, we introduce an intermediate language Zip (because it loosely resembles zippers from function programming).
The zipper remembers the last artifact above our currently translated subtree.
This artifact always exists in a well-formed option calculus expression.
The current parent will always be an artifact because it will never be an option because whenever we visit an option, we swap it with the artifact above.
Said artifact will then be the parent of the translated children again.

The zipper stores the children of the currently translated subtree.
It keeps track of which children have already been translated and which have not.
The idea is that the zipper wanders through the children from left to right, translating one child at a time.
In the beginning, no child of the parent artifact has been translated:

    [] ≪ e₁ ∷ e₂ ∷ e₃ ∷ ... ∷ eₙ

then, step by step, each child get's translated:

    b₁ ∷ [] ≪ e₂ ∷ e₃ ∷ ... ∷ eₙ
    b₁ ∷ b₂ ∷ [] ≪ e₃ ∷ ... ∷ eₙ
    b₁ ∷ b₂ ∷ b₃ ∷ [] ≪ ... ∷ eₙ
    ...
    b₁ ∷ b₂ ∷ b₃ ∷ ... ∷ bₙ ≪ []

The zipper is parameterized in a natural number that is the amount of children yet to translate.

This is in fact working just like "map" does on lists but we need the zipper to remember the already translated siblings to translate options.

The zipper does not store enough information to fully restore a tree from the current focus.
This limitation is intended to keep the structure as simple as possible and only as complex as necessary.
```agda
record Zip (work : ℕ) (i : Size) (A : 𝔸) : Set where
  -- In the paper, we write _⦇_≪_⦈ for this constructor.
  -- However, in Agda, using ⦇ and ⦈ is forbidden.
  constructor _-<_≪_>- --\T
  field
    parent    : atoms A
    siblingsL : List (2CC F ∞ A)
    siblingsR : Vec (OC F i A) work
open Zip public
infix 4 _-<_≪_>-

-- Curiously, Zip is itself a variability language (parameterized in the remaining work to do).
Zip-is-𝔼 : ℕ → Size → 𝔼
Zip-is-𝔼 = Zip

⟦_⟧ₜ : ∀ {w i} → 𝔼-Semantics V (OC.Configuration F) (Zip w i)
⟦ a -< ls ≪ rs >- ⟧ₜ c =
  let ⟦ls⟧ = map (flip ⟦_⟧₂ c) ls
      ⟦rs⟧ = ⟦ toList rs ⟧ₒ-recurse c
   in cons mkArtifact (a At.-< ⟦ls⟧ ++ ⟦rs⟧ >-)
```

## Translation as Big-Step Semantics

```agda
data _⊢_⟶ₒ_ :
  ∀ {n : ℕ} {A : 𝔸}
  → (i : Size) -- We have to make sizes explicit here because otherwise, Agda sometimes infers ∞ which makes termination checking fail.
  → Zip n i A
  → 2CC F ∞ A
  → Set
infix 3 _⊢_⟶ₒ_
data _⊢_⟶ₒ_ where
  {-|
  We finished translating a subtree. All work is done.
  We thus wrap up the zipper to the OC→2CCd subtree it represents.
  -}
  T-done :
    ∀ {i  : Size}
      {A  : 𝔸}
      {a  : atoms A}
      {ls : List (2CC F ∞ A)}
      --------------------------------------
    → i ⊢ a -< ls ≪ [] >- ⟶ₒ Artifact₂ a ls

  {-|
  If the next expression to OC→2CC is an artifact,
  we recursively proceed all its children (obtaining e₁)
  an then proceed with the remaining expressions (obtaining e₂).
  -}
  T-artifact :
    ∀ {i   : Size  }
      {n   : ℕ    }
      {A   : 𝔸}
      {a b : atoms A}
      {ls  : List (2CC F ∞    A)  }
      {es  : List (OC F    i  A)  }
      {rs  : Vec  (OC F (↑ i) A) n}
      {e₁  : 2CC F ∞ A}
      {e₂  : 2CC F ∞ A}
    →   i ⊢ b -< [] ≪ (fromList es) >-       ⟶ₒ e₁
    → ↑ i ⊢ a -< ls ∷ʳ e₁ ≪ rs >-            ⟶ₒ e₂
      ---------------------------------------------
    → ↑ i ⊢ a -< ls ≪ Artifactₒ b es ∷ rs >- ⟶ₒ e₂

  {-|
  If the next expression to OC→2CC is an option,
  we OC→2CC the current subtree once with the option picked (obtaining eᵒ⁻ʸ)
  and once without the option picked (obtaining eᵒ⁻ʸ).
  We can then put both results into a binary choice, where going left
  means picking the option, and going right means not picking the option.
  -}
  T-option :
    ∀ {i   : Size  }
      {n   : ℕ     }
      {A   : 𝔸     }
      {a   : atoms A}
      {O   : Option}
      {e   : OC F i A}
      {ls  : List (2CC F    ∞  A)  }
      {rs  : Vec (OC   F (↑ i) A) n}
      {eᵒ⁻ʸ : 2CC F ∞ A}
      {eᵒ⁻ⁿ : 2CC F ∞ A}
    → ↑ i ⊢ a -< ls ≪ e ∷ rs >-       ⟶ₒ eᵒ⁻ʸ
    → ↑ i ⊢ a -< ls ≪     rs >-       ⟶ₒ eᵒ⁻ⁿ
      ----------------------------------------------------
    → ↑ i ⊢ a -< ls ≪ O ❲ e ❳ ∷ rs >- ⟶ₒ O ⟨ eᵒ⁻ʸ , eᵒ⁻ⁿ ⟩

data _⟶_  :
  ∀ {i : Size} {A : 𝔸}
  → WFOC F i A
  → 2CC  F ∞ A
  → Set
infix 4 _⟶_
data _⟶_ where
  T-root :
    ∀ {i  : Size}
      {A  : 𝔸}
      {a  : atoms A}
      {es : List (OC F i A)}
      {e  : 2CC F ∞ A}
    → i ⊢ a -< [] ≪ (fromList es) >- ⟶ₒ e
      ------------------------------------
    → Root a es ⟶ e
```

## Determinism

Every OC expression is OC→2CCd to at most one 2CC expression.
```agda
⟶ₒ-is-deterministic : ∀ {n} {i} {A} {z : Zip n i A} {b b' : 2CC F ∞ A}
  → i ⊢ z ⟶ₒ b
  → i ⊢ z ⟶ₒ b'
    ------------
  → b ≡ b'
⟶ₒ-is-deterministic T-done T-done = refl
⟶ₒ-is-deterministic (T-artifact ⟶e₁ ⟶b)
                     (T-artifact ⟶e₂ ⟶b')
                     rewrite (⟶ₒ-is-deterministic ⟶e₁ ⟶e₂)
                     = ⟶ₒ-is-deterministic ⟶b ⟶b'
⟶ₒ-is-deterministic {z = a -< ls ≪ O ❲ _ ❳ ∷ _ >- } (T-option ⟶l₁ ⟶r₁) (T-option ⟶l₂ ⟶r₂) =
  let l₁≡l₂ = ⟶ₒ-is-deterministic ⟶l₁ ⟶l₂
      r₁≡r₂ = ⟶ₒ-is-deterministic ⟶r₁ ⟶r₂
   in Eq.cong₂ (O ⟨_,_⟩) l₁≡l₂ r₁≡r₂

⟶-is-deterministic : ∀ {i} {A} {e : WFOC F i A} {b b' : 2CC F ∞ A}
  → e ⟶ b
  → e ⟶ b'
    -------
  → b ≡ b'
⟶-is-deterministic (T-root ⟶b) (T-root ⟶b') = ⟶ₒ-is-deterministic ⟶b ⟶b'
```

## Totality (i.e., Progress)

Every OC expression is OC→2CCd to at least one 2CC expression.
Since we have already proven determinism, the proof for totality and thus a translation is unique.
```agda
Totalₒ : ∀ {n} {i} {A} → (e : Zip n i A) → Set
Totalₒ {i = i} e = ∃[ b ] (i ⊢ e ⟶ₒ b)

Total : ∀ {i} {A} → (e : WFOC F i A) → Set
Total {i} e = ∃[ b ] (e ⟶ b)

-- Smart constructor for Totalₒ that does not require naming the expression explicitly.
totalₒ : ∀ {n} {i} {A} {e : Zip n i A} {b}
  → (i ⊢ e ⟶ₒ b)
    -------------
  → Totalₒ e
totalₒ {b = b} r = b , r

⟶ₒ-is-total : ∀ {n} {i} {A}
  → (e : Zip n i A)
    ---------------
  → Totalₒ e
⟶ₒ-is-total (a -< ls ≪ [] >-) = totalₒ T-done
⟶ₒ-is-total (a -< ls ≪ Artifactₒ b es ∷ rs >-) =
  -- We must use "let" here and should not use "with".
  -- "with" forgets some information (I don't know what exactly) that
  -- makes the termination checker fail.
  let recursion-on-children-is-total = ⟶ₒ-is-total (b -< [] ≪ fromList es >-)
      e₁   = proj₁ recursion-on-children-is-total
      ⟶e₁ = proj₂ recursion-on-children-is-total
      ⟶e₂ = proj₂ (⟶ₒ-is-total (a -< ls ∷ʳ e₁ ≪ rs >-))
   in totalₒ (T-artifact ⟶e₁ ⟶e₂)
⟶ₒ-is-total (a -< ls ≪ O ❲ e ❳ ∷ rs >-)
  with ⟶ₒ-is-total (a -< ls ≪ e ∷ rs >-)
     | ⟶ₒ-is-total (a -< ls ≪     rs >-)
...  | _ , ⟶eᵒ⁻ʸ | _ , ⟶eᵒ⁻ⁿ = totalₒ (T-option ⟶eᵒ⁻ʸ ⟶eᵒ⁻ⁿ)

⟶-is-total : ∀ {i} {A}
  → (e : WFOC F i A)
    --------------
  → Total e
⟶-is-total (Root a es) =
  let rec = ⟶ₒ-is-total (a -< [] ≪ fromList es >-)
   in proj₁ rec , T-root (proj₂ rec)
```

## Preservation

Theorems:
```agda
preservesₒ :
  ∀ {n} {i} {A}
    {b : 2CC F ∞ A}
    {z : Zip n i A}
  → (c : OC.Configuration F)
  → i ⊢ z ⟶ₒ b
    -------------------
  → ⟦ z ⟧ₜ c ≡ ⟦ b ⟧₂ c

preserves :
  ∀ {i} {A}
    {b : 2CC F ∞ A}
    {e : WFOC F i A}
  → (c : OC.Configuration F)
  → e ⟶ b
    ------------------
  → ⟦ e ⟧ c ≡ ⟦ b ⟧₂ c
```

First, some auxiliary theorems that we need for the actual proofs of the preservation theorems.
```agda
open Data.Nat using (suc)
open Data.List using (catMaybes)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List.Properties using (++-identityʳ; ++-assoc; map-++)

{-|
The same as "preserves" (i.e., this functions implementation is copy and paste from "preserves").
The proof is actually just: preserves c (T-root ⟶e).
We need this auxiliary function to assist the termination checker because directly invoking "preserves" makes termination checking fail.
The problem is that we have to wrap ⟶e in T-root, which is a growing constructor, not a shrinking one.
Agda fails to see that "preserves" directly unpacks this constructor again and consequently, that the call is harmless.
Since Agda fails here, we have to avoid the re- and unpacking below T-root and thus introduce this auxiliary function.
-}
preserves-without-T-root :
  ∀ {i} {A} {b : atoms A} {es : List (OC F i A)} {e : 2CC F ∞ A}
  → (c : OC.Configuration F)
  → (⟶e : i ⊢ b -< [] ≪ fromList es >- ⟶ₒ e)
    ------------------------------------------
  → ⟦ Root b es ⟧ c ≡ ⟦ e ⟧₂ c
preserves-without-T-root {b = b} {es = es} {e = e} c ⟶e =
  let z = b -< [] ≪ (fromList es) >-
  in begin
       ⟦ Root b es ⟧ c
     ≡⟨⟩
       Artifactᵥ b (⟦ es ⟧ₒ-recurse c)
     ≡⟨ Eq.cong (λ eq → Artifactᵥ b (⟦ eq ⟧ₒ-recurse c)) (id≗toList∘fromList es) ⟩
       Artifactᵥ b (⟦ toList (fromList es) ⟧ₒ-recurse c)
     ≡⟨⟩
       ⟦ z ⟧ₜ c
     ≡⟨ preservesₒ c ⟶e ⟩
       ⟦ e ⟧₂ c
     ∎

{-|
This theorem ensures that making a step in the zipper (i.e., translating the next sub-expression)
preserves semantics.
The concrete formulas are a bit convoluted here because they are partially normalised.
-}
preservesₒ-artifact :
  ∀ {i} {A} {c}
    {b   : atoms A}
    {ls  : List (2CC F ∞ A)}
    {es  : List (OC F i A)}
    {e   : 2CC F ∞ A}
  → (rs  : List (V A))
  → (⟶e : i ⊢ b -< [] ≪ fromList es >- ⟶ₒ e)
    ----------------------------------------------------------------
  →   (map (flip ⟦_⟧₂ c) ls)             ++ ((⟦ Root b es ⟧ c) ∷ rs)
    ≡ (map (flip ⟦_⟧₂ c) (ls ++ e ∷ [])) ++ rs
preservesₒ-artifact {i} {A} {c} {b} {ls} {es} {e} rs ⟶e =
  let map₂     = map (flip ⟦_⟧₂ c)
      root-sem = ⟦ Root b es ⟧ c
   in begin
        map₂ ls ++ (root-sem ∷ rs)
      ≡⟨⟩
        map₂ ls ++ (root-sem ∷ [] ++ rs)
      ≡⟨ sym (++-assoc (map₂ ls) (root-sem ∷ []) rs) ⟩
        (map₂ ls ++ (root-sem ∷ [])) ++ rs
      -- apply induction hypothesis (root-sem preserves semantics)
      ≡⟨ Eq.cong (_++ rs)
          (Eq.cong (map₂ ls ++_)
            (Eq.cong (_∷ [])
              (preserves-without-T-root c ⟶e)))
      ⟩
        (map₂ ls ++ (map₂ (e ∷ []))) ++ rs
      ≡⟨ Eq.cong (_++ rs) (sym (map-++ (flip ⟦_⟧₂ c) ls (e ∷ []))) ⟩
        (map₂ (ls ++ e ∷ [])) ++ rs
      ∎

{-|
Auxiliary helper theorem for preservation of semantics for options, when an option is picked.
This helper theorem only proves that applying the semantics ⟦_⟧ₒ deep within the zipper semantics ⟦_⟧ₜ (normalised here)
does not care for the size of the expression.

We have to pattern match on e here so that Agda can observe that in any case ⟦_⟧ₒ yields the same value
irrespective of the size constraint of e.
We have to do this because ⟦_⟧ₒ could pattern on the size of e (in theory although this is not possible in practice).
So we show Agda that ⟦_⟧ₒ never does so.

This theorem has no real meaning and is rather a technical necessity.
-}
preservesₒ-option-size :
  ∀ {n} {i} {A} {c} {a : atoms A} {ls : List (2CC F ∞ A)} {rs : Vec (OC F (↑ i) A) n}
  → (e : OC F i A)
    -----------------------------------------------------------------------------------------------------
  →   Artifactᵥ a (map (flip ⟦_⟧₂ c) ls ++ catMaybes (⟦_⟧ₒ {i  } e c ∷ map (flip ⟦_⟧ₒ c) (toList rs)))
    ≡ Artifactᵥ a (map (flip ⟦_⟧₂ c) ls ++ catMaybes (⟦_⟧ₒ {↑ i} e c ∷ map (flip ⟦_⟧ₒ c) (toList rs)))
preservesₒ-option-size (Artifactₒ _ _) = refl
preservesₒ-option-size (_ ❲ _ ❳)       = refl
```

Actual proofs:
```agda
preservesₒ c (T-done {a = a} {ls = ls}) =
  let m = map (flip ⟦_⟧₂ c) ls
   in begin
        ⟦ a -< ls ≪ [] >- ⟧ₜ c
      ≡⟨⟩
        Artifactᵥ a (m ++ [])
      ≡⟨ Eq.cong (Artifactᵥ a) (++-identityʳ m) ⟩
        Artifactᵥ a m
      ≡⟨⟩
        ⟦ Artifact₂ a ls ⟧₂ c
      ∎
preservesₒ c (T-artifact {a = a} {b = b} {ls = ls} {es = es} {rs = rs} {e₁ = e₁} {e₂ = e₂} ⟶e ⟶b) =
  let all-rs = Artifactₒ b es ∷ rs
      z      = a -< ls ≪ all-rs >-
      map₂   = map (flip ⟦_⟧₂ c)
   in begin
        ⟦ z ⟧ₜ c
      ≡⟨⟩
        Artifactᵥ a (map₂ ls ++ ⟦ toList all-rs ⟧ₒ-recurse c)
      ≡⟨⟩
        Artifactᵥ a (map₂ ls ++ Artifactᵥ b (⟦ es ⟧ₒ-recurse c) ∷ ⟦ toList rs ⟧ₒ-recurse c)
      ≡⟨ Eq.cong (Artifactᵥ a) (preservesₒ-artifact (⟦ toList rs ⟧ₒ-recurse c) ⟶e) ⟩ -- prove that we can make a step
        Artifactᵥ a (map₂ (ls ++ e₁ ∷ []) ++ ⟦ toList rs ⟧ₒ-recurse c)
      ≡⟨⟩
        ⟦ a -< ls ∷ʳ e₁ ≪ rs >- ⟧ₜ c
      ≡⟨ preservesₒ c ⟶b ⟩ -- apply induction hypothesis
        ⟦ e₂ ⟧₂ c
      ∎
preservesₒ c (T-option {a = a} {O = O} {e = e} {ls = ls} {rs = rs} {eᵒ⁻ʸ = ey} {eᵒ⁻ⁿ = en} ⟶ey ⟶en) with c O
... | true  = begin
                Artifactᵥ a (map (flip ⟦_⟧₂ c) ls ++ (catMaybes (⟦ e ⟧ₒ c ∷ map (flip ⟦_⟧ₒ c) (toList rs))))
              ≡⟨ preservesₒ-option-size e ⟩ -- prove that size constraint on e does not matter for ⟦_⟧ₒ
                ⟦ a -< ls ≪ e ∷ rs >- ⟧ₜ c
              ≡⟨ preservesₒ c ⟶ey ⟩ -- apply induction hypothesis
                ⟦ ey ⟧₂ c
              ∎
... | false = begin
                ⟦ a -< ls ≪ rs >- ⟧ₜ c
              ≡⟨ preservesₒ c ⟶en ⟩ -- apply induction hypothesis
                ⟦ en ⟧₂ c
              ∎

preserves {b = b} {e = Root a es} c (T-root z⟶b) =
  let z = a -< [] ≪ (fromList es) >-
   in begin
        ⟦ Root a es ⟧ c
      ≡⟨⟩
        Artifactᵥ a (⟦ es ⟧ₒ-recurse c)
      ≡⟨ Eq.cong (λ eq → Artifactᵥ a (⟦ eq ⟧ₒ-recurse c)) (id≗toList∘fromList es) ⟩
        Artifactᵥ a (⟦ toList (fromList es) ⟧ₒ-recurse c)
      ≡⟨⟩
        ⟦ z ⟧ₜ c
      ≡⟨ preservesₒ c z⟶b ⟩ -- apply induction hypothesis
        ⟦ b ⟧₂ c
      ∎
```

## Translation Implementation

```agda
open import Framework.Compiler using (LanguageCompiler)
open import Framework.VariabilityLanguage
open import Framework.Relation.Expressiveness V
open import Framework.Relation.Function  using (_⇔_)

compile : ∀ {i : Size} {A : 𝔸} → WFOC F i A → 2CC F ∞ A
compile = proj₁ ∘ ⟶-is-total

compile-preserves : ∀ {i : Size} {A : 𝔸}
  → (e : WFOC F i A)
    ----------------------------
  → ⟦ e ⟧ ≅[ id ][ id ] ⟦ compile e ⟧₂
compile-preserves {i} {A} e = left , sym ∘ left -- this works because id is our config translation
  where
    left : ⟦ e ⟧ ⊆[ id ] ⟦ compile e ⟧₂
    left c =
      let trans      = ⟶-is-total e
          derivation = proj₂ trans
       in preserves c derivation

compile-configs : OC.Configuration F ⇔ 2CC.Configuration F
compile-configs = record { to = id ; from = id }

OC→2CC : LanguageCompiler (WFOCL F) (2CCL F)
OC→2CC = record
  { compile = compile
  ; config-compiler = λ _ → compile-configs
  ; preserves = compile-preserves
  }

2CC≽OC : 2CCL F ≽ (WFOCL F)
2CC≽OC = expressiveness-from-compiler OC→2CC
```
