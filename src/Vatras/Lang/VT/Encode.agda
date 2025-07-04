open import Vatras.Framework.Definitions
module Vatras.Lang.VT.Encode (F : 𝔽) where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; cong; cong₂)
open Eq.≡-Reasoning
open import Size using (∞)

open import Vatras.Framework.Variants using (Forest; Rose; _-<_>-; Variant-is-VL; VariantEncoder)
open import Vatras.Lang.VT F

open import Vatras.Data.EqIndexedSet using (_≅[_][_]_; irrelevant-index-≅)
open import Vatras.Framework.Relation.Function using (_⇔_; to; from)

mutual
  {-|
  Encodes a tree as a non-variational UnrootedVT.
  Configuring the resulting expression will always yield
  the input tree.
  To prove termination, this definition is an inlined variant of
    a -< map encode-tree xs >-
  -}
  encode-tree : ∀ {A} → Rose ∞ A → UnrootedVT A
  encode-tree (a -< xs >-) = a -< encode-forest xs >-

  {-|
  Encodes all trees in a forest to a non-variational
  UnrootedVT each, using 'encode-tree' defined above.
  To prove termination, this definition is an inlined variant of
    map encode-tree.
  -}
  encode-forest : ∀ {A} → Forest A → List (UnrootedVT A)
  encode-forest []       = []
  encode-forest (x ∷ xs) = encode-tree x ∷ encode-forest xs

encode : ∀ {A} → Forest A → VT A
encode x = if-true[ encode-forest x ]

mutual
  encode-tree-preserves : ∀ {A} → (T : Rose ∞ A) (c : Configuration)
    → configure (encode-tree T) c ≡ T ∷ []
  encode-tree-preserves (a -< xs >-) c = Eq.cong (λ x → (a -< x >- ∷ [])) (encode-forest-preserves xs c)

  encode-forest-preserves : ∀ {A} (V : Forest A) (c : Configuration)
    → configure-all (encode-forest V) c ≡ V
  encode-forest-preserves []       _ = refl
  encode-forest-preserves (x ∷ xs) c =
    begin
      configure-all (encode-forest (x ∷ xs)) c
    ≡⟨⟩
      configure (encode-tree x) c ++ configure-all (encode-forest xs) c
    ≡⟨ cong₂ _++_ (encode-tree-preserves x c) (encode-forest-preserves xs c) ⟩
      (x ∷ []) ++ xs
    ≡⟨⟩
      x ∷ xs
    ∎

encode-preserves : ∀ {A} (V : Forest A) (c : Configuration)
    → ⟦ encode V ⟧ c ≡ V
encode-preserves = encode-forest-preserves

{-|
Translating configurations is trivial because their values never matter.
We can do anything here.
-}
confs : ⊤ ⇔ Configuration
confs = record
  { to = λ where tt _ → true
  ; from = λ _ → tt
  }

preserves : ∀ {A} → (v : Forest A)
  → (λ _ → v) ≅[ to confs ][ from confs ] ⟦ encode v ⟧
preserves {A} v = irrelevant-index-≅ v
  (λ { tt → refl })
  (encode-preserves v)
  (to confs)
  (from confs)

encoder : VariantEncoder Forest VTL
encoder = record
  { compile = encode
  ; config-compiler = λ _ → confs
  ; preserves = preserves
  }
