open import Framework.Definitions
module Translation.Experiments.Choice-to-2Choice-Experiment where

open import Data.Nat using (ℕ)
open import Data.Nat.Show renaming (show to show-ℕ)
open import Data.List using (List; _∷_; []; map)
open import Data.List.NonEmpty using (List⁺; _∷_; length; toList) renaming (map to map⁺)
open import Data.Product using (proj₁; proj₂) renaming (_,_ to _and_)
open import Level using (_⊔_)
open import Function using (id)

import Relation.Binary.PropositionalEquality as Eq

open import Construct.Choices
open 2Choice using (_⟨_,_⟩)
open Choice using (_⟨_⟩)

open import Framework.Annotation.IndexedName
open import Translation.Construct.Choice-to-2Choice as Choice-to-2Choice
module Trans = Choice-to-2Choice.Translate

open import Util.Named
open import Test.Example
open import Test.Experiment
open import Show.Lines
open import Data.String using (String; _<+>_)

exp : Experiment (Choice.Syntax String ℕ)
getName exp = "Check N → 2 Choice trans"
get exp (name ≔ e) = do
 let open Trans ℕ using (convert; show-nested-choice)
 >         name <+> "=" <+> Choice.show id show-ℕ e
 > phantom name <+> "⇝" <+> show-nested-choice id show-ℕ (convert e)

un-ex : Example (Choice.Syntax String ℕ)
un-ex = "e₁" ≔ "D" ⟨ 0 ∷ [] ⟩

bi-ex : Example (Choice.Syntax String ℕ)
bi-ex = "e₂" ≔ "D" ⟨ 0 ∷ 1 ∷ [] ⟩

tri-ex : Example (Choice.Syntax String ℕ)
tri-ex = "e₃" ≔ "D" ⟨ 0 ∷ 1 ∷ 2 ∷ [] ⟩

many-ex : Example (Choice.Syntax String ℕ)
many-ex = "e₄" ≔ "D" ⟨ 0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ [] ⟩

all-ex : List (Example (Choice.Syntax String ℕ))
all-ex = un-ex ∷ bi-ex ∷ tri-ex ∷ many-ex ∷ []
