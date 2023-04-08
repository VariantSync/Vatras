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
open import Data.List using (List; _∷_; []; _∷ʳ_; _++_; length; map; catMaybes)
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Nat using (ℕ; suc; zero; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; <⇒≤)
open import Data.Product using (∃; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_; toList; fromList)
open import Size using (Size; Size<_; ↑_; ∞; _⊔ˢ_)
open import Function using (id; flip)

open import Lang.OC
     using ( OC; WFOC; Root; _❲_❳; ⟦_⟧; ⟦_⟧ₒ; ⟦_⟧ₒ-recurse; forgetWF; children-wf)
  renaming ( Artifact to Artifactₒ
           ; Configuration to Confₒ
           )
open import Lang.BCC
     using ( BCC; _⟨_,_⟩;
             BCC-is-bounded; BCC-is-weakenable
           )
  renaming ( ⟦_⟧ to ⟦_⟧₂
           ; Artifact to Artifact₂
           ; Configuration to Conf₂
           )
open import Lang.Annotation.Name using (Option; Dimension; _==_)
open import Definitions using (VarLang; Domain; Semantics; sequence-sized-artifact)
open import SemanticDomain using (Variant; Artifactᵥ)
open import Translation.Translation using
  (Translation; TranslationResult;
   expr;
   _⊆-via_; _⊇-via_; _≚-via_;
   _is-variant-preserving; translation-proves-variant-preservation)
open import Relations.Semantic using (_,_is-as-expressive-as_,_)

open import Util.AuxProofs using (m≤n⇒m<1+n; vec-n∸n)
open import Util.Existence using (∃-Size; ∃-syntax-with-type; _,_; proj₁; proj₂; ,-injectiveʳ)

open import Util.SizeJuggle using (to-max; sym-max)

open import Data.ConveyorBelt

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning
```

## Translation

What makes the translation hard?

1. Configuring Options globally: First my idea was, whenever we find an option, create a choice and evaluate the option to true for the left subtree and to false for the right subtree. Insight: This is already optimizing to avoid unnecessary nesting of duplicate choices. But nothing forces us to optimize _during_ a translation, more so because optimizations are only necessary if the input formula is un-optimized. Conclusion: Whenever we find an option, just translate it locally and continue (no global resolving of the option).
2. Reconstructing the tree:

```agda
{-
A partial zipper for the translation.
It stores some information about the context but not enough to fully restore a tree from the current focus.
This limitation is intended to keep the structure as simple as possible and only as complex as necessary.

The zipper remembers the last artefact above our currently translated subtree.
This artifact always exists in a well-formed option calculus expression.
The current parent will always be an artifact because it will never be an option because whenever we visit an option, we swap it with the artifact above.
Said artifact will then be the parent of the translated children again.

The zipper stores the children of the currently translated subtree in a ConveyorBelt.
This ConveyorBelt keeps track of which children have already been translated and which have not.
The parameter numChildren is the number of children of the current subtree.
The parameter numChildrenRight is the number of children yet to translate.
These children are to the right of the already translated children.
-}
record TZipper
  (i : Size)
  (A : Domain)
  (#cs #work : ℕ)
  (work≤cs : #work ≤ #cs) : Set where
  constructor _◀_ --\T
  field
    parent   : A
    siblings : ConveyorBelt (OC i A) (∃-Size[ j ] (BCC j A)) #work #cs work≤cs

-- TODO: Zulip: Ask if ∃-Size is the way to go for functions from sized types to sized types and when having to prove termination.

zip2bcc :
  ∀ {i : Size}
    {A : Domain}
  → (load left : ℕ)
  → (left≤load : left ≤ load)
  → TZipper i A load left left≤load
  → ∃-Size[ j ] (BCC j A)
zip2bcc {A = A} (suc load-1) (suc left-1) (s≤s left-1≤load-1) (a ◀ (ls ↢ O ❲ e ❳ ∷ rs)) =
   let i , l = zip2bcc (suc load-1) (suc left-1) (s≤s left-1≤load-1) (a ◀ (ls ↢ e ∷ rs))
       j , r = zip2bcc      load-1       left-1       left-1≤load-1  (a ◀ (ls ↢     rs))

       max-child-depth = i ⊔ˢ j
       choice-size = ↑ max-child-depth -- ↑ (i ⊔ˢ j)

       l-sized : BCC max-child-depth A
       l-sized = to-max BCC-is-weakenable i j l

       r-sized : BCC max-child-depth A
       r-sized = sym-max {BCC-is-bounded A} {j} {i} (to-max BCC-is-weakenable j i r)
    in
       choice-size , _⟨_,_⟩ {max-child-depth} O l-sized r-sized
zip2bcc (suc load-1) (suc left-1) (s≤s left-1≤load-1) (a ◀ belt@(ls ↢ Artifactₒ b es ∷ rs)) =
  let work = length es
      processedArtifact = zip2bcc work work ≤-refl (b ◀ putOnBelt es)
      left-1≤load : left-1 ≤ (suc load-1)
      left-1≤load = <⇒≤ (s≤s left-1≤load-1)
   in zip2bcc
        (suc load-1)
        left-1
        left-1≤load
        --(a ◀ (ls ∷ʳ processedArtifact ↢ rs))
        (a ◀ (step (λ _ → processedArtifact) belt))
zip2bcc {i = i} zero zero z≤n (a ◀ (    [] ↢ [])) =
  ↑ i , Artifact₂ a []
zip2bcc         load zero z≤n (a ◀ (l ∷ ls ↢ [])) =
  sequence-sized-artifact BCC-is-weakenable Artifact₂ a (l ∷ toList ls)

OCtoBCC : ∀ {i : Size} {A : Domain} → WFOC i A → ∃-Size[ j ] (BCC j A)
OCtoBCC (Root a es) =
  let work = length es
   in zip2bcc work work ≤-refl (a ◀ putOnBelt es)
```

```agda
record Zip (i : Size) (work : ℕ) (A : Domain) : Set where
  constructor _-<_◀_>- --\T
  field
    --{i j} : Size
    parent    : A
    siblingsL : List (BCC ∞ A) -- j
    siblingsR : Vec (OC i A) work -- i
open Zip public
infix 4 _-<_◀_>-

Zip-is-VarLang : ℕ → Definitions.VarLang
Zip-is-VarLang w = λ i → Zip i w

-- semantics of zippers (i.e., the intermediate translation state)
-- In fact, Zippers are also variability languages parameterized in amount of work to do.
⟦_⟧ₜ : ∀ {w : ℕ} → Semantics (Zip-is-VarLang w) Confₒ
⟦ a -< ls ◀ rs >- ⟧ₜ c =
  let ⟦ls⟧ = map (flip ⟦_⟧₂ c) ls
      ⟦rs⟧ = ⟦ toList rs ⟧ₒ-recurse c
   in Artifactᵥ a (⟦ls⟧ ++ ⟦rs⟧)

data _⊢_⟶ₒ_ :
  ∀ {n : ℕ} {A : Domain}
  → (i : Size)
  → Zip i n A
  → BCC ∞ A
  → Set
infix 3 _⊢_⟶ₒ_
data _⊢_⟶ₒ_ where
  T-done :
    ∀ {i  : Size}
      {A  : Domain}
      {a  : A}
      {ls : List (BCC ∞ A)}
      --------------------------------------
    → i ⊢ a -< ls ◀ [] >- ⟶ₒ Artifact₂ a ls

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

  T-option :
    ∀ {i   : Size  }
      {n   : ℕ    }
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

Function: Every OC expression is in relation to at most one BCC expression.
```agda
⟶ₒ-is-deterministic : ∀ {i} {n} {A} {z : Zip i n A} {b b' : BCC ∞ A}
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

## Totality (Progress)

Totality: Every OC expression is in relation to at least one BCC expression (Progress).
```agda
Totalₒ : ∀ {i} {n} {A} → (e : Zip i n A) → Set
Totalₒ {i} e = ∃[ b ] (i ⊢ e ⟶ₒ b)

-- smart constructor for Totalₒ
totalₒ : ∀ {i} {n} {A} {e : Zip i n A} {b}
  → (i ⊢ e ⟶ₒ b)
    -------------
  → Totalₒ e
totalₒ {b = b} r = b , r

⟶ₒ-is-total : ∀ {i} {n} {A}
  → (e : Zip i n A)
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
```

```agda
Total : ∀ {i} {A} → (e : WFOC i A) → Set
Total {i} e = ∃[ b ] (e ⟶ b)

⟶-is-total : ∀ {i} {A}
  → (e : WFOC i A)
    --------------
  → Total e
⟶-is-total (Root a es) =
  let rec = ⟶ₒ-is-total (a -< [] ◀ (fromList es) >-)
   in proj₁ rec , T-root (proj₂ rec)
```

## Preservation

```agda
open import Data.List.Properties using (++-identityʳ)

-- zipper preservation theorem for artifacts
helper : ∀ {A} {c} {i}
           {b : A}
           {ls : List (BCC ∞ A)}
           {es : List (OC i A)}
           {e  : BCC ∞ A}
           (rs : List (Variant A))
           (⟶e : i ⊢ b -< [] ◀ fromList es >- ⟶ₒ e)
         →   (map (flip ⟦_⟧₂ c) ls)             ++ (Artifactᵥ b (⟦ es ⟧ₒ-recurse c) ∷ rs)
           ≡ (map (flip ⟦_⟧₂ c) (ls ++ e ∷ [])) ++ rs
helper {A} {c} {i} {n} {b} {ls} {es} rs ⟶e = {!!}


preservesₒ :
  ∀ {i} {n} {A}
    {b : BCC ∞ A}
    {v : Variant A}
    {c : Confₒ}
    {z : Zip i n A}
  → v ≡ ⟦ z ⟧ₜ c
  → i ⊢ z ⟶ₒ b
    ------------
  → v ≡ ⟦ b ⟧₂ c
preservesₒ {c = c} refl (T-done {a = a} {ls = ls}) =
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
preservesₒ {c = c} refl (T-artifact {a = a} {b = b} {ls = ls} {es = es}
 {rs = rs} {e₁ = e₁}{e₂ = e₂} ⟶e ⟶b) =
  let all-rs = Artifactₒ b es ∷ rs
      z      = a -< ls ◀ all-rs >-
   in begin
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
    ≡⟨ Eq.cong (Artifactᵥ a) (helper (⟦ toList rs ⟧ₒ-recurse c) ⟶e) ⟩
      Artifactᵥ a
        (   map (flip ⟦_⟧₂ c) (ls ++ e₁ ∷ [])
         ++ ⟦ toList rs ⟧ₒ-recurse c
        )
    ≡⟨⟩
      ⟦ a -< ls ∷ʳ e₁ ◀ rs >- ⟧ₜ c
    ≡⟨ preservesₒ refl ⟶b ⟩
      ⟦ e₂ ⟧₂ c
    ∎
preservesₒ refl (T-option ⟶e ⟶b) = {!!}

preserves :
  ∀ {i} {A}
    {b : BCC ∞ A}
    {v : Variant A}
    {c : Confₒ}
    {e : WFOC i A}
  → v ≡ ⟦ e ⟧ c
  → e ⟶ b
    ------------
  → v ≡ ⟦ b ⟧₂ c
preserves {_} {_} {b} {.(⟦ Root a es ⟧ c)} {c} {Root a es} refl (T-root z⟶b) =
  let z = a -< [] ◀ (fromList es) >-
   in begin
        ⟦ Root a es ⟧ c
      ≡⟨⟩
        Artifactᵥ a (⟦ es ⟧ₒ-recurse c)
      ≡⟨ {!!} ⟩
        Artifactᵥ a (⟦ toList (fromList es) ⟧ₒ-recurse c)
      ≡⟨⟩
        ⟦ z ⟧ₜ c
      ≡⟨ preservesₒ refl z⟶b ⟩
        ⟦ b ⟧₂ c
      ∎
```


## Translation Implementation

```agda
translate : ∀ {i : Size} {A : Domain} → WFOC i A → TranslationResult A BCC Confₒ Conf₂
translate oc =
  --let j , bcc = OCtoBCC oc in
  let bcc , trace = ⟶-is-total oc in
  record
  { size = ∞ --j
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


## Proofs

```agda
WFOC→BCC-left : ∀ {i : Size} {A : Domain}
  → (e : WFOC i A)
    --------------
  → e ⊆-via OC→BCC

WFOC→BCC-right : ∀ {i : Size} {A : Domain}
  → (e : WFOC i A)
    --------------
  → e ⊇-via OC→BCC

OC→BCC-is-variant-preserving : OC→BCC is-variant-preserving
OC→BCC-is-variant-preserving e = WFOC→BCC-left e , WFOC→BCC-right e

BCC-is-as-expressive-as-OC : BCC , ⟦_⟧₂ is-as-expressive-as WFOC , ⟦_⟧
BCC-is-as-expressive-as-OC = translation-proves-variant-preservation OC→BCC OC→BCC-is-variant-preserving
```

## via relation

```agda
WFOC→BCC-left e c =
  let trans      = ⟶-is-total e
      derivation = proj₂ trans
   in preserves refl derivation
```

## via function
```text
open import Data.Vec using (Vec; cast; fromList)
open Data.Nat using (_∸_)
open import Data.Product.Properties using ()

es-size : ∀ {i : Size} {A : Domain} {L : Definitions.VarLang} (es : List (L i A)) → Size
es-size {i = i} _ = i

-- foo : ∀
    -- zip2bcc l-es l-es ≤-refl (a ◀ (vec-n∸n l-es ↢ head ∷ fromList tail))

WFOC→BCC-left {i} {A} r@(Root a []) cₒ = refl
WFOC→BCC-left {i} {A} r@(Root a es@(Artifactₒ a' a'-es ∷ tail)) cₒ = {!!}
WFOC→BCC-left {i} {A} r@(Root a es@(O ❲ head ❳ ∷ tail)) cₒ =
-- WFOC→BCC-left {i} {A} r@(Root a es@(_ ∷ _)) cₒ =
  let l-es = length es

      result : ∃-Size[ j ] (BCC j A)
      result = OCtoBCC r
      result-size : Size
      result-size = proj₁ result
      result-expr : BCC result-size A
      result-expr = proj₂ result
  in
  begin
    ⟦ r ⟧ cₒ
  ≡⟨⟩
    Artifactᵥ a (⟦ es ⟧ₒ-recurse cₒ)
  ≡⟨ Eq.cong (Artifactᵥ a) refl ⟩
    Artifactᵥ a (catMaybes (map (λ x → ⟦ x ⟧ₒ cₒ) es))
  ≡⟨ {!!} ⟩
    -- ⟦ proj₂ (zip2bcc l-es l-es ≤-refl (a ◀ (vec-n∸n l-es ↢ head ∷ fromList tail))) ⟧₂ cₒ
  -- ≡⟨⟩
    ⟦ proj₂ (zip2bcc l-es l-es ≤-refl (a ◀ (vec-n∸n l-es ↢ fromList es))) ⟧₂ cₒ
  ≡⟨ Eq.cong (Function.flip ⟦_⟧₂ cₒ) {result-expr} {result-expr} refl ⟩ -- For some reason, we have to pass at least one implicit argument here to Eq.cong but I have not idea why and it took too much time to figure that out. -- (,-injectiveʳ {BCC j A} {j} {j} refl) ⟩
    ⟦ proj₂ (zip2bcc l-es l-es ≤-refl (a ◀ putOnBelt es)) ⟧₂ cₒ
  ≡⟨⟩
    ⟦ result-expr ⟧₂ cₒ
  ∎
```

```text
-- When the translation of configurations is id, then the theorems for both sides become equivalent.
-- TODO: Maybe we want to gerneralize this observation to the framework?
WFOC→BCC-right = WFOC→BCC-left
```

