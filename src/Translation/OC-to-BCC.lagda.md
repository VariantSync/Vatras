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
open import Data.Bool using (if_then_else_)
open import Data.List using (List; _∷_; []; _∷ʳ_; _++_; length; map; catMaybes)
open import Data.Nat using (ℕ)
open import Data.Product using (∃; ∃-syntax; _,_; proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_; toList; fromList)
open import Size using (Size; ↑_; ∞)
open import Function using (id; flip)

open import Definitions using (VarLang; Domain; Semantics)
open import Lang.Annotation.Name using (Option)
open import Lang.OC
     using ( OC; WFOC; Root; _❲_❳; ⟦_⟧; ⟦_⟧ₒ; ⟦_⟧ₒ-recurse)
  renaming ( Artifact to Artifactₒ
           ; Configuration to Confₒ
           )
open import Lang.BCC
     using ( BCC; _⟨_,_⟩)
  renaming ( ⟦_⟧ to ⟦_⟧₂
           ; Artifact to Artifact₂
           ; Configuration to Conf₂
           )
open import Relations.Semantic using (_,_is-as-expressive-as_,_)
open import SemanticDomain using (Variant; Artifactᵥ)
open import Translation.Translation using
  (Translation; TranslationResult;
   _⊆-via_;
   _is-variant-preserving; _is-semantics-preserving;
   translation-proves-variant-preservation)

open import Util.AuxProofs using (id≗toList∘fromList)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
```

## Zipper

For the translation of options, we have to remember translated children within the subtree we are currently translating.
Therefore, we introduce a (partial) zipper.
The zipper remembers the last artefact above our currently translated subtree.
This artifact always exists in a well-formed option calculus expression.
The current parent will always be an artifact because it will never be an option because whenever we visit an option, we swap it with the artifact above.
Said artifact will then be the parent of the translated children again.

The zipper stores the children of the currently translated subtree.
It keeps track of which children have already been translated and which have not.
The idea is that the zipper wanders through the children from left to right, translating one child at a time.
In the beginning, no child of the parent artifact has been translated:

    [] ◀ e₁ ∷ e₂ ∷ e₃ ∷ ... ∷ eₙ

then, step by step, each child get's translated:

    b₁ ∷ [] ◀ e₂ ∷ e₃ ∷ ... ∷ eₙ
    b₁ ∷ b₂ ∷ [] ◀ e₃ ∷ ... ∷ eₙ
    b₁ ∷ b₂ ∷ b₃ ∷ [] ◀ ... ∷ eₙ
    ...
    b₁ ∷ b₂ ∷ b₃ ∷ ... ∷ bₙ ◀ []

The zipper is parameterized in a natural number that is the amount of children yet to translate.

This is in fact working just like "map" does on lists but we need the zipper to remember the already translated siblings to translate options.

The zipper does not store enough information to fully restore a tree from the current focus.
This limitation is intended to keep the structure as simple as possible and only as complex as necessary.
```agda
record Zip (work : ℕ) (i : Size) (A : Domain) : Set where
  constructor _-<_◀_>- --\T
  field
    parent    : A
    siblingsL : List (BCC ∞ A)
    siblingsR : Vec (OC i A) work
open Zip public
infix 4 _-<_◀_>-

-- Curiously, Zip is itself a variability language (parameterized in the remaining work to do).
Zip-is-VarLang : ℕ → VarLang
Zip-is-VarLang = Zip

⟦_⟧ₜ : ∀ {w : ℕ} → Semantics (Zip w) Confₒ
⟦ a -< ls ◀ rs >- ⟧ₜ c =
  let ⟦ls⟧ = map (flip ⟦_⟧₂ c) ls
      ⟦rs⟧ = ⟦ toList rs ⟧ₒ-recurse c
   in Artifactᵥ a (⟦ls⟧ ++ ⟦rs⟧)
```

## Translation as Big-Step Semantics

```agda
data _⊢_⟶ₒ_ :
  ∀ {n : ℕ} {A : Domain}
  → (i : Size) -- We have to make sizes explicit here because otherwise, Agda sometimes infers ∞ which makes termination checking fail.
  → Zip n i A
  → BCC ∞ A
  → Set
infix 3 _⊢_⟶ₒ_
data _⊢_⟶ₒ_ where
  {-|
  We finished translating a subtree. All work is done.
  We thus wrap up the zipper to the translated subtree it represents.
  -}
  T-done :
    ∀ {i  : Size}
      {A  : Domain}
      {a  : A}
      {ls : List (BCC ∞ A)}
      --------------------------------------
    → i ⊢ a -< ls ◀ [] >- ⟶ₒ Artifact₂ a ls

  {-|
  If the next expression to translate is an artifact,
  we recursively proceed all its children (obtaining e₁)
  an then proceed with the remaining expressions (obtaining e₂).
  -}
  T-artifact :
    ∀ {i   : Size  }
      {n   : ℕ    }
      {A   : Domain}
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
  If the next expression to translate is an option,
  we translate the current subtree once with the option picked (obtaining eᵒ⁻ʸ)
  and once without the option picked (obtaining eᵒ⁻ʸ).
  We can then put both results into a binary choice, where going left
  means picking the option, and going right means not picking the option.
  -}
  T-option :
    ∀ {i   : Size  }
      {n   : ℕ     }
      {A   : Domain}
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
  ∀ {i : Size} {A : Domain}
  → WFOC i A
  → BCC ∞ A
  → Set
infix 4 _⟶_
data _⟶_ where
  T-root :
    ∀ {i  : Size}
      {A  : Domain}
      {a  : A}
      {es : List (OC i A)}
      {e  : BCC ∞ A}
    → i ⊢ a -< [] ◀ (fromList es) >- ⟶ₒ e
      ------------------------------------
    → Root a es ⟶ e
```

## Determinism

Every OC expression is translated to at most one BCC expression.
```agda
⟶ₒ-is-deterministic : ∀ {n} {i} {A} {z : Zip n i A} {b b' : BCC ∞ A}
  → i ⊢ z ⟶ₒ b
  → i ⊢ z ⟶ₒ b'
    ----------
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

Every OC expression is translated to at least one BCC expression.
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
  -- We must use "let" here and are should not use "with".
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

```agda
open import Data.List.Properties using (++-identityʳ)

-- zipper preservation theorem for artifacts
preservesₒ-artifact :
         ∀ {i} {A} {c}
           {b   : A}
           {ls  : List (BCC ∞ A)}
           {es  : List (OC i A)}
           {e   : BCC ∞ A}
           (rs  : List (Variant A))
           (⟶e : i ⊢ b -< [] ◀ fromList es >- ⟶ₒ e)
         →   (map (flip ⟦_⟧₂ c) ls)             ++ (Artifactᵥ b (⟦ es ⟧ₒ-recurse c) ∷ rs)
           ≡ (map (flip ⟦_⟧₂ c) (ls ++ e ∷ [])) ++ rs
preservesₒ-artifact {A} {c} {i} {n} {b} {ls} {es} rs ⟶e = {!!}

preservesₒ :
  ∀ {n} {i} {A}
    {b : BCC ∞ A}
    {c : Confₒ}
    {z : Zip n i A}
  → i ⊢ z ⟶ₒ b
    -------------------
  → ⟦ z ⟧ₜ c ≡ ⟦ b ⟧₂ c
preservesₒ {c = c} (T-done {a = a} {ls = ls}) =
  begin
    ⟦ a -< ls ◀ [] >- ⟧ₜ c
  ≡⟨⟩
    Artifactᵥ a ((map (flip ⟦_⟧₂ c) ls) ++ [])
  ≡⟨ Eq.cong
       (Artifactᵥ a)
       (++-identityʳ
         (map (flip ⟦_⟧₂ c) ls))
   ⟩
    Artifactᵥ a (map (flip ⟦_⟧₂ c) ls)
  ∎
preservesₒ {c = c} (T-artifact {a = a} {b = b} {ls = ls} {es = es} {rs = rs} {e₁ = e₁}{e₂ = e₂} ⟶e ⟶b) =
  let all-rs = Artifactₒ b es ∷ rs
      z      = a -< ls ◀ all-rs >-
  in
  begin
    ⟦ z ⟧ₜ c
  ≡⟨⟩
    Artifactᵥ a
      (   map (flip ⟦_⟧₂ c) ls
       ++ ⟦ toList all-rs ⟧ₒ-recurse c
      )
  ≡⟨⟩
    Artifactᵥ a
      (   map (flip ⟦_⟧₂ c) ls
       ++ Artifactᵥ b (⟦ es ⟧ₒ-recurse c) ∷ ⟦ toList rs ⟧ₒ-recurse c
      )
  ≡⟨ Eq.cong (Artifactᵥ a) (preservesₒ-artifact (⟦ toList rs ⟧ₒ-recurse c) ⟶e) ⟩
    Artifactᵥ a
      (   map (flip ⟦_⟧₂ c) (ls ++ e₁ ∷ [])
       ++ ⟦ toList rs ⟧ₒ-recurse c
      )
  ≡⟨⟩
    ⟦ a -< ls ∷ʳ e₁ ◀ rs >- ⟧ₜ c
  ≡⟨ preservesₒ ⟶b ⟩
    ⟦ e₂ ⟧₂ c
  ∎
preservesₒ {c = c} (T-option {_} {_} {_} {a} {O} {e} {ls} {rs} {ey} {en} ⟶ey ⟶en) =
  let all-rs = O ❲ e ❳ ∷ rs
      z = a -< ls ◀ all-rs >-
  in
  begin
    ⟦ z ⟧ₜ c
  ≡⟨⟩
    Artifactᵥ a
      (   (map (flip ⟦_⟧₂ c) ls)
       ++ (⟦ toList all-rs ⟧ₒ-recurse c))
  ≡⟨ {!!} ⟩ -- Do case analysis on (c O) here.
    ⟦ if c O then ey else en ⟧₂ c
  ≡⟨⟩
    ⟦ O ⟨ ey , en ⟩ ⟧₂ c
  ∎

preserves :
  ∀ {i} {A}
    {b : BCC ∞ A}
    {c : Confₒ}
    {e : WFOC i A}
  → e ⟶ b
    ------------------
  → ⟦ e ⟧ c ≡ ⟦ b ⟧₂ c
preserves {_} {_} {b} {c} {Root a es} (T-root z⟶b) =
  let z = a -< [] ◀ (fromList es) >-
   in begin
        ⟦ Root a es ⟧ c
      ≡⟨⟩
        Artifactᵥ a (⟦ es ⟧ₒ-recurse c)
      ≡⟨ Eq.cong (λ eq → Artifactᵥ a (⟦ eq ⟧ₒ-recurse c)) (id≗toList∘fromList es) ⟩
        Artifactᵥ a (⟦ toList (fromList es) ⟧ₒ-recurse c)
      ≡⟨⟩
        ⟦ z ⟧ₜ c
      ≡⟨ preservesₒ z⟶b ⟩
        ⟦ b ⟧₂ c
      ∎
```

## Translation Implementation

```agda
translate : ∀ {i} {A} → WFOC i A → TranslationResult A BCC Confₒ Conf₂
translate oc =
  let bcc , trace = ⟶-is-total oc in
  record
  { size = ∞
  ; expr = bcc
  ; conf = id
  ; fnoc = id
  }

OC→BCC : Translation WFOC BCC Confₒ Conf₂
OC→BCC = record
  { sem₁ = ⟦_⟧
  ; sem₂ = ⟦_⟧₂
  ; translate = translate
  }
```

## Conclusions

```agda
⊆-via-OC→BCC : ∀ {i : Size} {A : Domain}
  → (e : WFOC i A)
    --------------
  → e ⊆-via OC→BCC
⊆-via-OC→BCC e c =
  let trans      = ⟶-is-total e
      derivation = proj₂ trans
   in preserves derivation

-- When the translation of configurations is id, then the theorems for both sides become equivalent.
-- TODO: Maybe we want to gerneralize this observation to the framework?
OC→BCC-is-variant-preserving : OC→BCC is-variant-preserving
OC→BCC-is-variant-preserving e = ⊆-via-OC→BCC e , ⊆-via-OC→BCC e

OC→BCC-is-semantics-preserving : OC→BCC is-semantics-preserving
OC→BCC-is-semantics-preserving = OC→BCC-is-variant-preserving , λ e c → refl

BCC-is-as-expressive-as-OC : BCC , ⟦_⟧₂ is-as-expressive-as WFOC , ⟦_⟧
BCC-is-as-expressive-as-OC = translation-proves-variant-preservation OC→BCC OC→BCC-is-variant-preserving
```

