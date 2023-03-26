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
open import Data.Nat using (ℕ; suc; zero; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; <⇒≤)
open import Data.Product using (∃; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Vec using ([]; _∷_; _∷ʳ_; toList)
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
    siblings : ConveyorBelt (OC i A) (∃-Size[ j ] (BCC j A)) #cs #work work≤cs

zip2bcc :
  ∀ {i : Size}
    {A : Domain}
  → (load left : ℕ)
  → (left≤load : left ≤ load)
  → TZipper i A load left left≤load
  → ∃-Size[ j ] (BCC j A)
zip2bcc {A = A} (suc load-1) (suc left-1) (s≤s left≤load-1) (a ◀ (ls ↢ O ❲ e ❳ ∷ rs)) =
   let i , l = zip2bcc (suc load-1) (suc left-1) (s≤s left≤load-1) (a ◀ (ls ↢ e ∷ rs))
       j , r = zip2bcc      load-1       left-1       left≤load-1  (a ◀ (ls ↢     rs))

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
-- foo : ∀ {i} {A} {j : Size< i} {a : A} {es : List (OC j A)}
--         {c₁ = cₒ} →
--       Artifactᵥ a (catMaybes (map (λ x → ⟦ x ⟧ₒ cₒ) es)) ≡
--       ⟦ proj₂ (zip2bcc (length es) (length es) ≤-refl (a ◀ putOnBelt es)) ⟧₂ cₒ
-- foo = {!!}

open import Data.Vec using (Vec; cast; fromList)
open Data.Nat using (_∸_)
open import Data.Product.Properties using ()

bar : ∀ {A : Domain} {i : Size} (a : A) (es : List (OC i A))
 →   zip2bcc (length es) (length es) ≤-refl (a ◀ (vec-n∸n (length es) ↢ fromList es))
   ≡ zip2bcc (length es) (length es) ≤-refl (a ◀ putOnBelt es)
bar a es = refl

es-size : ∀ {i : Size} {A : Domain} {L : Definitions.VarLang} (es : List (L i A)) → Size
es-size {i = i} _ = i

WFOC→BCC-left {i} {A} r@(Root a es) cₒ =
  let l-es = length es
      -- i-es = es-size es

      pair : ∃-Size[ j ] (BCC j A)
      pair = OCtoBCC r
      j : Size
      j = proj₁ pair
      r' : BCC j A
      r' = proj₂ pair

      --∃-Size[ j' ] (BCC j' A) ≡ ∃-Size[ j ] (BCC j A)
      lel = bar a es
  in
  begin
    ⟦ r ⟧ cₒ
  ≡⟨⟩
    Artifactᵥ a (⟦ es ⟧ₒ-recurse cₒ)
  ≡⟨ Eq.cong (Artifactᵥ a) refl ⟩
    Artifactᵥ a (catMaybes (map (λ x → ⟦ x ⟧ₒ cₒ) es))
  ≡⟨ {!!} ⟩
    --⟦ proj₂ (zip2bcc l-es l-es ≤-refl (a ◀ (vec-n∸n l-es ↢ fromList es))) ⟧₂ cₒ
  --≡⟨ Eq.cong (λ x → ⟦ x ⟧₂ cₒ) (,-injectiveʳ {BCC } {i = j} {j = j} refl) ⟩
    ⟦ proj₂ (zip2bcc l-es l-es ≤-refl (a ◀ putOnBelt es)) ⟧₂ cₒ
  ≡⟨⟩
    ⟦ r' ⟧₂ cₒ
  ∎
```

```agda
-- When the translation of configurations is id, then the theorems for both sides become equivalent.
-- TODO: Maybe we want to gerneralize this observation to the framework?
WFOC→BCC-right = WFOC→BCC-left
```

