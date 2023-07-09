# Relating Option Calculus to Binary Choice Calculus

## Options

```agda
{-# OPTIONS --sized-types #-}
{-# OPTIONS --allow-unsolved-metas #-}
```

## Module

```agda
module Translation.OC-to-BCC where
```

## Imports

```agda
open import Data.Bool using (if_then_else_; true; false)
open import Data.List using (List; _∷_; []; _∷ʳ_; _++_; length; map; catMaybes)
open import Data.Nat using (ℕ)
open import Data.Product using (∃; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_; toList; fromList)
open import Size using (Size; ↑_; _⊔ˢ_; ∞)
open import Function using (id; flip)

open import Framework.Definitions
open import Framework.Annotation.Name using (Option)
open import Lang.OC
     using ( OC; WFOC; WFOCL; Root; _❲_❳; ⟦_⟧; ⟦_⟧ₒ; ⟦_⟧ₒ-recurse)
  renaming ( Artifact to Artifactₒ
           ; Configuration to Confₒ
           )
open import Lang.BCC
     using ( BCC; BCCL; _⟨_,_⟩)
  renaming ( ⟦_⟧ to ⟦_⟧₂
           ; Artifact to Artifact₂
           ; Configuration to Conf₂
           )
open import Framework.Relation.Expressiveness using (_≽_)
open import Framework.Proof.Translation using
  (Translation; TranslationResult;
   _⊆-via_;
   _is-variant-preserving; _is-semantics-preserving;
   expressiveness-by-translation)

open import Util.AuxProofs using (id≗toList∘fromList)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
```

## Zipper

For the translation of options, we have to remember OC→BCCd children within the subtree we are currently translating.
Therefore, we introduce a (partial) zipper.
The zipper remembers the last artefact above our currently OC→BCCd subtree.
This artifact always exists in a well-formed option calculus expression.
The current parent will always be an artifact because it will never be an option because whenever we visit an option, we swap it with the artifact above.
Said artifact will then be the parent of the OC→BCCd children again.

The zipper stores the children of the currently OC→BCCd subtree.
It keeps track of which children have already been OC→BCCd and which have not.
The idea is that the zipper wanders through the children from left to right, translating one child at a time.
In the beginning, no child of the parent artifact has been OC→BCCd:

    [] ◀ e₁ ∷ e₂ ∷ e₃ ∷ ... ∷ eₙ

then, step by step, each child get's OC→BCCd:

    b₁ ∷ [] ◀ e₂ ∷ e₃ ∷ ... ∷ eₙ
    b₁ ∷ b₂ ∷ [] ◀ e₃ ∷ ... ∷ eₙ
    b₁ ∷ b₂ ∷ b₃ ∷ [] ◀ ... ∷ eₙ
    ...
    b₁ ∷ b₂ ∷ b₃ ∷ ... ∷ bₙ ◀ []

The zipper is parameterized in a natural number that is the amount of children yet to OC→BCC.

This is in fact working just like "map" does on lists but we need the zipper to remember the already OC→BCCd siblings to OC→BCC options.

The zipper does not store enough information to fully restore a tree from the current focus.
This limitation is intended to keep the structure as simple as possible and only as complex as necessary.
```agda
record Zip (work : ℕ) (i : Size) (A : 𝔸) : Set where
  constructor _-<_◀_>- --\T
  field
    parent    : A
    siblingsL : List (BCC ∞ A)
    siblingsR : Vec (OC i A) work
open Zip public
infix 4 _-<_◀_>-

-- Curiously, Zip is itself a variability language (parameterized in the remaining work to do).
Zip-is-𝕃 : ℕ → 𝕃
Zip-is-𝕃 = Zip

⟦_⟧ₜ : ∀ {w : ℕ} → Semantics (Zip w) Confₒ
⟦ a -< ls ◀ rs >- ⟧ₜ c =
  let ⟦ls⟧ = map (flip ⟦_⟧₂ c) ls
      ⟦rs⟧ = ⟦ toList rs ⟧ₒ-recurse c
   in Artifactᵥ a (⟦ls⟧ ++ ⟦rs⟧)
```

## Translation as Big-Step Semantics

```agda
data _⊢_⟶ₒ_ :
  ∀ {n : ℕ} {A : 𝔸}
  → (i : Size) -- We have to make sizes explicit here because otherwise, Agda sometimes infers ∞ which makes termination checking fail.
  → Zip n i A
  → BCC ∞ A
  → Set
infix 3 _⊢_⟶ₒ_
data _⊢_⟶ₒ_ where
  {-|
  We finished translating a subtree. All work is done.
  We thus wrap up the zipper to the OC→BCCd subtree it represents.
  -}
  T-done :
    ∀ {i  : Size}
      {A  : 𝔸}
      {a  : A}
      {ls : List (BCC ∞ A)}
      --------------------------------------
    → i ⊢ a -< ls ◀ [] >- ⟶ₒ Artifact₂ a ls

  {-|
  If the next expression to OC→BCC is an artifact,
  we recursively proceed all its children (obtaining e₁)
  an then proceed with the remaining expressions (obtaining e₂).
  -}
  T-artifact :
    ∀ {i   : Size  }
      {n   : ℕ    }
      {A   : 𝔸}
      {a b : A     }
      {ls  : List (BCC ∞    A)  }
      {es  : List (OC    i  A)  }
      {rs  : Vec  (OC (↑ i) A) n}
      {e₁  : BCC ∞ A}
      {e₂  : BCC ∞ A}
    →   i ⊢ b -< [] ◀ (fromList es) >-       ⟶ₒ e₁
    → ↑ i ⊢ a -< ls ∷ʳ e₁ ◀ rs >-            ⟶ₒ e₂
      ---------------------------------------------
    → ↑ i ⊢ a -< ls ◀ Artifactₒ b es ∷ rs >- ⟶ₒ e₂

  {-|
  If the next expression to OC→BCC is an option,
  we OC→BCC the current subtree once with the option picked (obtaining eᵒ⁻ʸ)
  and once without the option picked (obtaining eᵒ⁻ʸ).
  We can then put both results into a binary choice, where going left
  means picking the option, and going right means not picking the option.
  -}
  T-option :
    ∀ {i   : Size  }
      {n   : ℕ     }
      {A   : 𝔸}
      {a   : A     }
      {O   : Option}
      {e   : OC i A}
      {ls  : List (BCC ∞ A)    }
      {rs  : Vec (OC (↑ i) A) n}
      {eᵒ⁻ʸ : BCC ∞ A}
      {eᵒ⁻ⁿ : BCC ∞ A}
    → ↑ i ⊢ a -< ls ◀ e ∷ rs >-       ⟶ₒ eᵒ⁻ʸ
    → ↑ i ⊢ a -< ls ◀     rs >-       ⟶ₒ eᵒ⁻ⁿ
      ----------------------------------------------------
    → ↑ i ⊢ a -< ls ◀ O ❲ e ❳ ∷ rs >- ⟶ₒ O ⟨ eᵒ⁻ʸ , eᵒ⁻ⁿ ⟩

data _⟶_  :
  ∀ {i : Size} {A : 𝔸}
  → WFOC i A
  → BCC ∞ A
  → Set
infix 4 _⟶_
data _⟶_ where
  T-root :
    ∀ {i  : Size}
      {A  : 𝔸}
      {a  : A}
      {es : List (OC i A)}
      {e  : BCC ∞ A}
    → i ⊢ a -< [] ◀ (fromList es) >- ⟶ₒ e
      ------------------------------------
    → Root a es ⟶ e
```

## Determinism

Every OC expression is OC→BCCd to at most one BCC expression.
```agda
⟶ₒ-is-deterministic : ∀ {n} {i} {A} {z : Zip n i A} {b b' : BCC ∞ A}
  → i ⊢ z ⟶ₒ b
  → i ⊢ z ⟶ₒ b'
    ------------
  → b ≡ b'
⟶ₒ-is-deterministic T-done T-done = refl
⟶ₒ-is-deterministic (T-artifact ⟶e₁ ⟶b)
                     (T-artifact ⟶e₂ ⟶b')
                     rewrite (⟶ₒ-is-deterministic ⟶e₁ ⟶e₂)
                     = ⟶ₒ-is-deterministic ⟶b ⟶b'
⟶ₒ-is-deterministic {z = a -< ls ◀ O ❲ _ ❳ ∷ _ >- } (T-option ⟶l₁ ⟶r₁) (T-option ⟶l₂ ⟶r₂) =
  let l₁≡l₂ = ⟶ₒ-is-deterministic ⟶l₁ ⟶l₂
      r₁≡r₂ = ⟶ₒ-is-deterministic ⟶r₁ ⟶r₂
   in Eq.cong₂ (O ⟨_,_⟩) l₁≡l₂ r₁≡r₂

⟶-is-deterministic : ∀ {i} {A} {e : WFOC i A} {b b' : BCC ∞ A}
  → e ⟶ b
  → e ⟶ b'
    -------
  → b ≡ b'
⟶-is-deterministic (T-root ⟶b) (T-root ⟶b') = ⟶ₒ-is-deterministic ⟶b ⟶b'
```

## Totality (i.e., Progress)

Every OC expression is OC→BCCd to at least one BCC expression.
Since we have already proven determinism, the proof for totality and thus a translation is unique.
```agda
Totalₒ : ∀ {n} {i} {A} → (e : Zip n i A) → Set
Totalₒ {i = i} e = ∃[ b ] (i ⊢ e ⟶ₒ b)

Total : ∀ {i} {A} → (e : WFOC i A) → Set
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
⟶ₒ-is-total (a -< ls ◀ [] >-) = totalₒ T-done
⟶ₒ-is-total (a -< ls ◀ Artifactₒ b es ∷ rs >-) =
  -- We must use "let" here and should not use "with".
  -- "with" forgets some information (I don't know what exactly) that
  -- makes the termination checker fail.
  let recursion-on-children-is-total = ⟶ₒ-is-total (b -< [] ◀ fromList es >-)
      e₁   = proj₁ recursion-on-children-is-total
      ⟶e₁ = proj₂ recursion-on-children-is-total
      ⟶e₂ = proj₂ (⟶ₒ-is-total (a -< ls ∷ʳ e₁ ◀ rs >-))
   in totalₒ (T-artifact ⟶e₁ ⟶e₂)
⟶ₒ-is-total (a -< ls ◀ O ❲ e ❳ ∷ rs >-)
  with ⟶ₒ-is-total (a -< ls ◀ e ∷ rs >-)
     | ⟶ₒ-is-total (a -< ls ◀     rs >-)
...  | _ , ⟶eᵒ⁻ʸ | _ , ⟶eᵒ⁻ⁿ = totalₒ (T-option ⟶eᵒ⁻ʸ ⟶eᵒ⁻ⁿ)

⟶-is-total : ∀ {i} {A}
  → (e : WFOC i A)
    --------------
  → Total e
⟶-is-total (Root a es) =
  let rec = ⟶ₒ-is-total (a -< [] ◀ fromList es >-)
   in proj₁ rec , T-root (proj₂ rec)
```

## Preservation

Theorems:
```agda
preservesₒ :
  ∀ {n} {i} {A}
    {b : BCC ∞ A}
    {z : Zip n i A}
  → (c : Confₒ)
  → i ⊢ z ⟶ₒ b
    -------------------
  → ⟦ z ⟧ₜ c ≡ ⟦ b ⟧₂ c

preserves :
  ∀ {i} {A}
    {b : BCC ∞ A}
    {e : WFOC i A}
  → (c : Confₒ)
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
  ∀ {i} {A} {b : A} {es : List (OC i A)} {e : BCC ∞ A}
  → (c : Confₒ)
  → (⟶e : i ⊢ b -< [] ◀ fromList es >- ⟶ₒ e)
    ------------------------------------------
  → ⟦ Root b es ⟧ c ≡ ⟦ e ⟧₂ c
preserves-without-T-root {b = b} {es = es} {e = e} c ⟶e =
  let z = b -< [] ◀ (fromList es) >-
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
    {b   : A}
    {ls  : List (BCC ∞ A)}
    {es  : List (OC i A)}
    {e   : BCC ∞ A}
  → (rs  : List (Variant ∞ A))
  → (⟶e : i ⊢ b -< [] ◀ fromList es >- ⟶ₒ e)
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
      ≡⟨ Eq.sym (++-assoc (map₂ ls) (root-sem ∷ []) rs) ⟩
        (map₂ ls ++ (root-sem ∷ [])) ++ rs
      -- apply induction hypothesis (root-sem preserves semantics)
      ≡⟨ Eq.cong (_++ rs)
          (Eq.cong (map₂ ls ++_)
            (Eq.cong (_∷ [])
              (preserves-without-T-root c ⟶e)))
      ⟩
        (map₂ ls ++ (map₂ (e ∷ []))) ++ rs
      ≡⟨ Eq.cong (_++ rs) (Eq.sym (map-++ (flip ⟦_⟧₂ c) ls (e ∷ []))) ⟩
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
  ∀ {n} {i} {A} {c} {a : A} {ls : List (BCC ∞ A)} {rs : Vec (OC (↑ i) A) n}
  → (e : OC i A)
    -----------------------------------------------------------------------------------------------------
  →   Artifactᵥ a (map (flip ⟦_⟧₂ c) ls ++ catMaybes (⟦_⟧ₒ {i  } {A} e c ∷ map (flip ⟦_⟧ₒ c) (toList rs)))
    ≡ Artifactᵥ a (map (flip ⟦_⟧₂ c) ls ++ catMaybes (⟦_⟧ₒ {↑ i} {A} e c ∷ map (flip ⟦_⟧ₒ c) (toList rs)))
preservesₒ-option-size (Artifactₒ _ _) = refl
preservesₒ-option-size (_ ❲ _ ❳)       = refl
```

Actual proofs:
```agda
preservesₒ c (T-done {a = a} {ls = ls}) =
  let m = map (flip ⟦_⟧₂ c) ls
   in begin
        ⟦ a -< ls ◀ [] >- ⟧ₜ c
      ≡⟨⟩
        Artifactᵥ a (m ++ [])
      ≡⟨ Eq.cong (Artifactᵥ a) (++-identityʳ m) ⟩
        Artifactᵥ a m
      ≡⟨⟩
        ⟦ Artifact₂ a ls ⟧₂ c
      ∎
preservesₒ c (T-artifact {a = a} {b = b} {ls = ls} {es = es} {rs = rs} {e₁ = e₁} {e₂ = e₂} ⟶e ⟶b) =
  let all-rs = Artifactₒ b es ∷ rs
      z      = a -< ls ◀ all-rs >-
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
        ⟦ a -< ls ∷ʳ e₁ ◀ rs >- ⟧ₜ c
      ≡⟨ preservesₒ c ⟶b ⟩ -- apply induction hypothesis
        ⟦ e₂ ⟧₂ c
      ∎
preservesₒ c (T-option {a = a} {O = O} {e = e} {ls = ls} {rs = rs} {eᵒ⁻ʸ = ey} {eᵒ⁻ⁿ = en} ⟶ey ⟶en) with c O
... | true  = begin
                Artifactᵥ a (map (flip ⟦_⟧₂ c) ls ++ (catMaybes (⟦ e ⟧ₒ c ∷ map (flip ⟦_⟧ₒ c) (toList rs))))
              ≡⟨ preservesₒ-option-size e ⟩ -- prove that size constraint on e does not matter for ⟦_⟧ₒ
                ⟦ a -< ls ◀ e ∷ rs >- ⟧ₜ c
              ≡⟨ preservesₒ c ⟶ey ⟩ -- apply induction hypothesis
                ⟦ ey ⟧₂ c
              ∎
... | false = begin
                ⟦ a -< ls ◀ rs >- ⟧ₜ c
              ≡⟨ preservesₒ c ⟶en ⟩ -- apply induction hypothesis
                ⟦ en ⟧₂ c
              ∎

preserves {b = b} {e = Root a es} c (T-root z⟶b) =
  let z = a -< [] ◀ (fromList es) >-
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
OC→BCC : Translation WFOCL BCCL
OC→BCC oc =
  let bcc , trace = ⟶-is-total oc in
  record
  { size = ∞
  ; expr = bcc
  ; conf = id
  ; fnoc = id
  }
```

## Conclusions

```agda
⊆-via-OC→BCC : ∀ {i : Size} {A : 𝔸}
  → (e : WFOC i A)
    --------------
  → e ⊆-via OC→BCC
⊆-via-OC→BCC e c =
  let trans      = ⟶-is-total e
      derivation = proj₂ trans
   in preserves c derivation

-- When the translation of configurations is id, then the theorems for both sides become equivalent.
-- TODO: Maybe we want to gerneralize this observation to the framework?
OC→BCC-is-variant-preserving : OC→BCC is-variant-preserving
OC→BCC-is-variant-preserving e = ⊆-via-OC→BCC (get e) , ⊆-via-OC→BCC (get e)

OC→BCC-is-semantics-preserving : OC→BCC is-semantics-preserving
OC→BCC-is-semantics-preserving = OC→BCC-is-variant-preserving , λ e c → refl

BCC-is-at-least-as-expressive-as-OC : BCCL ≽ WFOCL
BCC-is-at-least-as-expressive-as-OC = expressiveness-by-translation OC→BCC OC→BCC-is-variant-preserving
```

