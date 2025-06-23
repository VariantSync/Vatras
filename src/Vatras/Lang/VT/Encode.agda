open import Vatras.Framework.Definitions
module Vatras.Lang.VT.Encode (F : 𝔽) where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_; map; concat; concatMap)
open import Data.List.Properties using (concatMap-map)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open Eq.≡-Reasoning
open import Size using (∞)
open import Function using (_∘_)

open import Vatras.Framework.Variants using (Forest; Rose; _-<_>-; Variant-is-VL; VariantEncoder)
open import Vatras.Lang.VT F

open import Vatras.Data.EqIndexedSet using (_≅[_][_]_; irrelevant-index-≅)
open import Vatras.Framework.Relation.Function using (_⇔_; to; from)
open import Vatras.Framework.VariabilityLanguage using (Semantics; Config)

{-|
Encodes a tree as a non-variational UnrootedVT.
Configuring the resulting expression will always yield
the input tree.
-}
{-# TERMINATING #-}
encode-tree : ∀ {A} → Rose ∞ A → UnrootedVT A
encode-tree (a -< cs >-) = a -< map encode-tree cs >-

{-|
Encodes all trees in a forest to a non-variational
UnrootedVT each, using 'encode-tree' defined above.
-}
encode-forest : ∀ {A} → Forest A → List (UnrootedVT A)
encode-forest = map encode-tree

encode : ∀ {A} → Forest A → VT A
encode x = if-true[ encode-forest x ]

mutual
  encode-tree-preserves : ∀ {A} → (T : Rose ∞ A) (c : Configuration)
    → configure c (encode-tree T) ≡ T ∷ []
  encode-tree-preserves (a -< cs >-) c = Eq.cong (λ eq → (a -< eq >-) ∷ []) (encode-forest-preserves cs c)

  encode-forest-preserves : ∀ {A} (V : Forest A) (c : Configuration)
    → configure-all c (encode-forest V) ≡ V
  encode-forest-preserves [] _ = refl
  encode-forest-preserves (x ∷ xs) c =
    begin
      configure-all c (encode-forest (x ∷ xs))
    ≡⟨⟩
      configure-all c (map encode-tree (x ∷ xs))
    ≡⟨⟩
      concatMap (configure c) (map encode-tree (x ∷ xs))
    ≡⟨ concatMap-map (configure c) (encode-tree) (x ∷ xs) ⟩
      concatMap (configure c ∘ encode-tree) (x ∷ xs)
    ≡⟨⟩
      concat ((configure c (encode-tree x) ∷ map (configure c ∘ encode-tree) xs))
    ≡⟨⟩
      (configure c (encode-tree x)) ++ (concatMap (configure c ∘ encode-tree) xs)
    ≡⟨ Eq.cong (_++ _) (encode-tree-preserves x c) ⟩
      (x ∷ []) ++ (concatMap (configure c ∘ encode-tree) xs)
    ≡⟨⟩
      x ∷ (concatMap (configure c ∘ encode-tree) xs)
    ≡⟨ Eq.cong (x ∷_) (concatMap-map (configure c) encode-tree xs) ⟨
      x ∷ (concatMap (configure c) (map encode-tree xs))
    ≡⟨ Eq.cong (x ∷_) (encode-forest-preserves xs c) ⟩
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
