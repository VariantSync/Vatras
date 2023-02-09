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
     using ( BCC; _⟨_,_⟩)
  renaming ( ⟦_⟧ to ⟦_⟧₂
           ; Artifact to Artifact₂
           ; Configuration to Conf₂
           )
open import Lang.Annotation.Name using (Option; Dimension; _==_)
open import Translation.Translation
     using (Domain; Translation; TranslationResult)
     using (sequence-sized-artifact)
open import Util.Existence using (∃-Size; _,_)

open import Data.ReversedList using ([]; _∷_)
open import Data.ConveyorBelt
```

## Translation

What makes the translation hard?

1. Configuring Options globally: First my idea was, whenever we find an option, create a choice and evaluate the option to true for the left subtree and to false for the right subtree. Insight: This is already optimizing to avoid unnecessary nesting of duplicate choices. But nothing forces us to optimize _during_ a translation, more so because optimizations are only necessary if the input formula is un-optimized. Conclusion: Whenever we find an option, just translate it locally and continue (no global resolving of the option).
2. Reconstructing the tree:

```agda
-- PartialConf : Set
-- PartialConf = String → Maybe Bool

-- partialOC-Eval : ∀ {i : Size} {A : Domain} → PartialConf → OC i A → Maybe (OC i A)
-- partialOC-Eval c (Artifactₒ a es) = {!!}
-- partialOC-Eval c (O ❲ e ❳) with c O
-- ... | just b  = if b
--                 then partialOC-Eval c e
--                 else nothing
-- ... | nothing = mapm (λ e' → O ❲ e' ❳) (partialOC-Eval c e)

-- weaken-bound : ∀ {i : Size} {A : Domain} → OC i A → OC (↑ i) A
-- weaken-bound e = e

-- select-option : ∀ {i : Size} {A : Domain} → Option → OC i A → OC i A
-- select-option O (Artifactₒ a es) = Artifactₒ a (mapl (select-option O) es)
-- select-option O (O' ❲ e ❳) = let e' = select-option O e in
--                              if O == O'
--                              then weaken-bound e'
--                              else O' ❲ e' ❳

-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (inspect)

-- select-option-wf : ∀ {i : Size} {A : Domain} → Option → WFOC i A → WFOC i A
-- select-option-wf O (Root a es) with select-option O (Artifactₒ a es) | inspect (select-option O) (Artifactₒ a es)
-- ... | Artifactₒ a' es' | _ = Root a' es'

-- deselect-option : ∀ {i : Size} {A : Domain} → Option → OC i A → Maybe (OC i A)
-- deselect-option O (Artifactₒ a es) = just (Artifactₒ a (catMaybes (mapl (deselect-option O) es)))
-- deselect-option O (O' ❲ e ❳) = if O == O'
--                                then nothing
--                                else mapm (λ x → O' ❲ x ❳) (deselect-option O e)

-- deselect-option-wf : ∀ {i : Size} {A : Domain} → Option → WFOC i A → WFOC i A
-- deselect-option-wf O (Root a es) with deselect-option O (Artifactₒ a es) | inspect (deselect-option O) (Artifactₒ a es)
-- ... | just (Artifactₒ a' es') | _ = Root a' es'

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

max : ∀ (i j : Size) → Size
max = _⊔ˢ_

i<↑i : (i : Size) → Size< (↑ i)
i<↑i i = i -- Do not eta reduce. It confuses Agda.

upcast : ∀ {A : Domain} (i j : Size) → BCC i A → BCC (max i j) A
upcast _ _ e = e

swap : ∀ {A : Domain} → (i j : Size) → BCC (i<↑i (max i j)) A → BCC (i<↑i (max j i)) A
swap _ _ e = e

recast : ∀ {A : Domain} (i j : Size) → BCC i A → BCC (i<↑i (max i j)) A
recast _ _ e = e

open import Util.Existence using (proj₁)

{-# TERMINATING #-}
OCtoBCC' : ∀ {i : Size} {A : Domain} → TZipper i A → ∃-Size[ j ] (BCC j A)
OCtoBCC' {A = A} (a ◀ (ls ↢ O ❲ e ❳ ∷ rs)) =
   let i , l = OCtoBCC' (a ◀ (ls ↢ e ∷ rs))
       j , r = OCtoBCC' (a ◀ (ls ↢     rs))
       choice-size : Size
       choice-size = ↑ (max i j)
       alternatives-size : Size< choice-size
       alternatives-size = i<↑i (max i j)

       l-sized : BCC alternatives-size A
       l-sized = recast i j l
       r-sized : BCC alternatives-size A
       r-sized = swap j i (recast j i r)
    in
       choice-size , _⟨_,_⟩ {choice-size} {alternatives-size} O l-sized r-sized
OCtoBCC' (a ◀ (ls ↢ Artifactₒ b es ∷ rs)) =
  let processedArtifact = OCtoBCC' (b ◀ putOnBelt es) in
  OCtoBCC' (a ◀ (ls ∷ processedArtifact ↢ rs))
OCtoBCC' {i = i} (a ◀ (    [] ↢ [])) =
  ↑ i , Artifact₂ a []
OCtoBCC'         (a ◀ (ls ∷ l ↢ [])) =
  let asList⁺ = Data.ReversedList.toList⁺ (ls ∷ l) in
  sequence-sized-artifact Artifact₂ a asList⁺

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

