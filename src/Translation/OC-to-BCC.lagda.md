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
open import Data.String using (String)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapm)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _∷_; []; reverse; _++_; catMaybes) renaming (map to mapl)
open import Data.List.NonEmpty using (List⁺; _∷_)
open import Data.Product using (_×_; _,_)
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
open import Translation.Translation using (Translation; TranslationResult)
open import Util.Existence using (∃-Size; _,_)
open import Util.SizeJuggle using (i<↑i; weaken-to-smaller-↑max; sym-smaller-↑max)

open import Data.ReversedList using ([]; _∷_)
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
-}
record TZipper (i : Size) (A : Domain) : Set where
  constructor _◀_ --\T
  field
    parent   : A
    siblings : ConveyorBelt (OC i A) (∃-Size[ j ] (BCC j A))

{-# TERMINATING #-}
OCtoBCC' : ∀ {i : Size} {A : Domain} → TZipper i A → ∃-Size[ j ] (BCC j A)
OCtoBCC' {A = A} (a ◀ (ls ↢ O ❲ e ❳ ∷ rs)) =
   let i , l = OCtoBCC' (a ◀ (ls ↢ e ∷ rs))
       j , r = OCtoBCC' (a ◀ (ls ↢     rs))

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
OCtoBCC' (a ◀ (ls ↢ Artifactₒ b es ∷ rs)) =
  let processedArtifact = OCtoBCC' (b ◀ putOnBelt es) in
  OCtoBCC' (a ◀ (ls ∷ processedArtifact ↢ rs))
OCtoBCC' {i = i} (a ◀ (    [] ↢ [])) =
  ↑ i , Artifact₂ a []
OCtoBCC'         (a ◀ (ls ∷ l ↢ [])) =
  let asList⁺ = Data.ReversedList.toList⁺ (ls ∷ l) in
  sequence-sized-artifact BCC-is-weakenable Artifact₂ a asList⁺

-- Todo: remove temp ∞
OCtoBCC : ∀ {i : Size} {A : Domain} → WFOC i A → ∃-Size[ j ] (BCC j A)
OCtoBCC (Root a es) = OCtoBCC' (a ◀ putOnBelt es)

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

