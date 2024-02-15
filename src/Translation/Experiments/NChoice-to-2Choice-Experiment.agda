{-# OPTIONS --sized-types #-}

open import Framework.Definitions
module Translation.Experiments.NChoice-to-2Choice-Experiment where

open import Data.Nat using (ℕ)
open import Data.Nat.Show renaming (show to show-ℕ)
open import Data.List using (List; _∷_; []; map)
open import Data.List.NonEmpty using (List⁺; _∷_; length; toList) renaming (map to map⁺)
open import Data.Product using (proj₁; proj₂) renaming (_,_ to _and_)
open import Level using (_⊔_)
open import Function using (id)

import Relation.Binary.PropositionalEquality as Eq

open import Construct.Choices as Chc
open Chc.Choice₂
  using (_⟨_,_⟩)
  renaming
    (Syntax to 2Choice
    ; Standard-Semantics to ⟦_⟧₂
    ; Config to Config₂
    ; show to show-2choice
    )
open Chc.Choiceₙ
  using (_⟨_⟩)
  renaming
    (Syntax to NChoice
    ; Standard-Semantics to ⟦_⟧ₙ
    ; Config to Configₙ
    ; show to show-nchoice
    )

open import Framework.Annotation.IndexedName
open import Translation.Construct.NChoice-to-2Choice as N→2
module Trans = N→2.Translate

open import Util.Named
open import Test.Example
open import Test.Experiment
open import Show.Lines
open import Data.String using (String; _<+>_)

exp : Experiment (NChoice String ℕ)
getName exp = "Check N → 2 Choice trans"
get exp (name ≔ e) = do
 let open Trans (Eq.setoid ℕ) using (convert; show-nested-choice)
 >         name <+> "=" <+> show-nchoice id show-ℕ e
 > phantom name <+> "⇝" <+> show-nested-choice id show-ℕ (convert e)

un-ex : Example (NChoice String ℕ)
un-ex = "e₁" ≔ "D" ⟨ 0 ∷ [] ⟩

bi-ex : Example (NChoice String ℕ)
bi-ex = "e₂" ≔ "D" ⟨ 0 ∷ 1 ∷ [] ⟩

tri-ex : Example (NChoice String ℕ)
tri-ex = "e₃" ≔ "D" ⟨ 0 ∷ 1 ∷ 2 ∷ [] ⟩

many-ex : Example (NChoice String ℕ)
many-ex = "e₄" ≔ "D" ⟨ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ [] ⟩

all-ex : List (Example (NChoice String ℕ))
all-ex = un-ex ∷ bi-ex ∷ tri-ex ∷ many-ex ∷ []
