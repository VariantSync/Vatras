# Relating Option Calculus to Binary Choice Calculus

## Options

```agda
{-# OPTIONS --sized-types #-}
```

## Module

```agda
module Translation.OC-to-BCC where
```

## Imports

```agda
open import Data.List using (List; []; length)
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Nat using (ℕ; suc; zero; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; <⇒≤)
open import Data.Product using (∃; ∃-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Vec using ([]; _∷_; _∷ʳ_; toList)
open import Size using (Size; Size<_; ↑_; ∞; _⊔ˢ_)
open import Function using (id)

open import Lang.OC
     using ( OC; WFOC; Root; _❲_❳; forgetWF; children-wf)
  renaming ( ⟦_⟧ to ⟦_⟧ₒ
           ; Artifact to Artifactₒ
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
open import Translation.Translation using (Translation; TranslationResult; _⊆-via_; _⊇-via_; _≚-via_; _is-variant-preserving; translation-proves-variant-preservation)
open import Relations.Semantic using (_,_is-as-expressive-as_,_)

open import Util.AuxProofs using (m≤n⇒m<1+n)
open import Util.Existence using (∃-Size; ∃-syntax-with-type; _,_)

open import Util.SizeJuggle using (i<↑i; weaken-to-smaller-↑max; sym-smaller-↑max)

open import Data.ConveyorBelt
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
  (numChildren numChildrenRight : ℕ)
  (numChildren≤numChildrenRight : numChildrenRight ≤ numChildren) : Set where
  constructor _◀_ --\T
  field
    parent   : A
    siblings : ConveyorBelt (OC i A) (∃-Size[ j ] (BCC j A)) numChildren numChildrenRight numChildren≤numChildrenRight

OCtoBCC' :
  ∀ {i : Size}
    {A : Domain}
  → (load left : ℕ)
  → (left≤load : left ≤ load)
  → TZipper i A load left left≤load
  → ∃-Size[ j ] (BCC j A)
OCtoBCC' {A = A} (suc load-1) (suc left-1) (s≤s load-1≤left-1) (a ◀ (ls ↢ O ❲ e ❳ ∷ rs)) =
   let i , l = OCtoBCC' (suc load-1) (suc left-1) (s≤s load-1≤left-1) (a ◀ (ls ↢ e ∷ rs))
       j , r = OCtoBCC'      load-1       left-1       load-1≤left-1  (a ◀ (ls ↢     rs))

       -- Unfortunately, we have to help the type-checker a lot with the sizes.
       -- In other proofs this just worked out of the box but here we have to use lots of safe type casting to turn the sizes into the right types.
       max-child-depth : Size
       max-child-depth = i ⊔ˢ j

       choice-size : Size
       choice-size = ↑ max-child-depth -- ↑ (i ⊔ˢ j)

       -- Prove that max-child-depth is indeed smaller than choice-size.
       alternatives-size : Size< choice-size
       alternatives-size = i<↑i max-child-depth

       l-sized : BCC alternatives-size A
       l-sized = weaken-to-smaller-↑max BCC-is-weakenable i j l

       r-sized : BCC alternatives-size A
       r-sized = sym-smaller-↑max (BCC-is-bounded A) j i (weaken-to-smaller-↑max BCC-is-weakenable j i r)
    in
       choice-size , _⟨_,_⟩ {choice-size} {alternatives-size} O l-sized r-sized
OCtoBCC' (suc load-1) (suc left-1) (s≤s left-1≤load-1) (a ◀ belt@(ls ↢ Artifactₒ b es ∷ rs)) =
  let work = length es
      processedArtifact = OCtoBCC' work work ≤-refl (b ◀ putOnBelt es)
      left-1≤load : left-1 ≤ (suc load-1)
      left-1≤load = <⇒≤ (s≤s left-1≤load-1)
   in OCtoBCC'
        (suc load-1)
        left-1
        left-1≤load
        --(a ◀ (ls ∷ʳ processedArtifact ↢ rs))
        (a ◀ (step (λ _ → processedArtifact) belt))
OCtoBCC' {i = i} zero zero z≤n (a ◀ (    [] ↢ [])) =
  ↑ i , Artifact₂ a []
OCtoBCC'         load zero z≤n (a ◀ (l ∷ ls ↢ [])) =
  sequence-sized-artifact BCC-is-weakenable Artifact₂ a (l ∷ toList ls)

OCtoBCC : ∀ {i : Size} {A : Domain} → WFOC i A → ∃-Size[ j ] (BCC j A)
OCtoBCC (Root a es) =
  let work = length es
   in OCtoBCC' work work ≤-refl (a ◀ putOnBelt es)

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
  { sem₁ = ⟦_⟧ₒ
  ; sem₂ = ⟦_⟧₂
  ; translate = translate
  }
```


