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
open import Data.List using (List; _∷_; []; length; map; catMaybes)
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Nat using (ℕ; suc; zero; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; <⇒≤)
open import Data.Product using (∃; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Vec using (Vec; []; _∷_; _∷ʳ_; toList)
open import Size using (Size; Size<_; ↑_; ∞; _⊔ˢ_)
open import Function using (id)

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
open import Definitions using (Domain; sequence-sized-artifact)
open import SemanticDomain using (Artifactᵥ)
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

record Zip
  (A : Domain)
  (#cs #work : ℕ)
  (work≤cs : #work ≤ #cs) : Set where
  constructor _X_ --\T
  field
    {i j} : Size
    parent   : A
    siblings : ConveyorBelt (OC i A) (BCC j A) #work #cs work≤cs

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

data _OF_LEFT-TODO_⊢_⟶_ {A : Domain} :
    (left load : ℕ)
  → (left≤load : left ≤ load)
  → Zip A load left left≤load
  → ∃-Size[ j ] (BCC j A)
  → Set
  where
  T-leaf :
    ∀ {i : Size}
      (a : A)
      ---------------------------------------------------------------------
    → zero OF zero LEFT-TODO z≤n ⊢ a X ([] ↢ []) ⟶ (↑ i , Artifact₂ a [])

  T-done :
    ∀ {i : Size}
      (load-1 : ℕ)
      (a : A)
      (l : BCC i A)
      (ls : Vec (BCC i A) load-1)
      --------------------------------------------------------------------------------------------
    → zero OF suc load-1 LEFT-TODO z≤n ⊢ a X (l ∷ ls ↢ []) ⟶ (↑ i , Artifact₂ a (l ∷ toList ls))

  T-artifact :
    ∀ {i i-e₁ i-e₂ : Size}
      (left-1 load-1 : ℕ)
      (left-1≤load-1 : left-1 ≤ load-1)
      (a b : A)
      (es : List (OC i A))
      (rs : Vec (OC (↑ i) A) left-1)
      (ls : Vec (BCC i-e₁ A) (load-1 ∸ left-1))
      (e₁ : BCC i-e₁ A)
      (e₂ : BCC i-e₂ A)
    →  length es OF  length es LEFT-TODO           ≤-refl        ⊢ b X (putOnBelt es)                               ⟶ (i-e₁ , e₁)
    →     left-1 OF suc load-1 LEFT-TODO <⇒≤ (s≤s left-1≤load-1) ⊢ a X (step (λ _ → e₁) (ls ↢ Artifactₒ b es ∷ rs)) ⟶ (i-e₂ , e₂)
      -----------------------------------------------------------------------------------------------------------------------------
    → suc left-1 OF suc load-1 LEFT-TODO      s≤s left-1≤load-1  ⊢ a X (ls ↢ Artifactₒ b es ∷ rs)                   ⟶ (i-e₂ , e₂)

  T-option :
    ∀ {i j k l : Size}
      (left-1 load-1 : ℕ)
      (left-1≤load-1 : left-1 ≤ load-1)
      (O : Option)
      (a : A)
      (e : OC k A)
      (rs : Vec (OC (↑ k) A) left-1)
      (ls : Vec (BCC l A) (load-1 ∸ left-1))
      (eᵒ⁻ʸ : BCC i A)
      (eᵒ⁻ⁿ : BCC j A)
    → suc left-1 OF suc load-1 LEFT-TODO s≤s left-1≤load-1 ⊢ a X (ls ↢ e ∷ rs)       ⟶ (i , eᵒ⁻ʸ)
    →     left-1 OF     load-1 LEFT-TODO     left-1≤load-1 ⊢ a X (ls ↢     rs)       ⟶ (j , eᵒ⁻ⁿ)
      ---------------------------------------------------------------------------------------------------------------------------
    → suc left-1 OF suc load-1 LEFT-TODO s≤s left-1≤load-1 ⊢ a X (ls ↢ O ❲ e ❳ ∷ rs) ⟶ (↑ (i ⊔ˢ j) , _⟨_,_⟩ {i ⊔ˢ j} O eᵒ⁻ʸ eᵒ⁻ⁿ)

data _⟶_ {A : Domain} :
  ∀ {i : Size}
  → WFOC i A
  → ∃-Size[ j ] (BCC j A)
  → Set
  where
  T-root :
    ∀ {i : Size}
      (a : A)
      (es : List (OC i A))
      (e : ∃-Size[ j ] (BCC j A))
    → length es OF length es LEFT-TODO ≤-refl ⊢ a X (putOnBelt es) ⟶ e
      -----------------------------------------------------------------
    → Root a es ⟶ e

OCtoBCC : ∀ {i : Size} {A : Domain} → WFOC i A → ∃-Size[ j ] (BCC j A)
OCtoBCC (Root a es) =
  let work = length es
   in zip2bcc work work ≤-refl (a ◀ putOnBelt es)

translate : ∀ {i : Size} {A : Domain} → WFOC i A → TranslationResult A BCC Confₒ Conf₂
translate oc =
  let j , bcc = OCtoBCC oc in
  record
  { size = j
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

```agda
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

```agda
-- When the translation of configurations is id, then the theorems for both sides become equivalent.
-- TODO: Maybe we want to gerneralize this observation to the framework?
WFOC→BCC-right = WFOC→BCC-left
```

