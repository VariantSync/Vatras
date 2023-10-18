{-# OPTIONS --sized-types #-}

module Framework.V2.Lang.2ADT where

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)
open import Function using (id)
open import Size using (Size; ↑_)

open import Framework.V2.Definitions
open import Framework.V2.Constructs.GrulerArtifacts
open import Framework.V2.Constructs.Choices
open import Framework.V2.Variants using (GrulerVariant)

private
  BinaryChoice = VLChoice₂.Syntax
  BinaryChoice-Semantics = VLChoice₂.Semantics

data 2ADT : Size → 𝔼 where
  2ADTAsset  : ∀ {i A} → Leaf A → 2ADT i A
  2ADTChoice : ∀ {i A} → BinaryChoice ℕ (2ADT i) A → 2ADT (↑ i) A

semantics : ∀ {i : Size} → 𝔼-Semantics GrulerVariant ℕ Bool (2ADT i)

2ADTVL : ∀ {i : Size} → VariabilityLanguage GrulerVariant ℕ Bool
2ADTVL {i} = syn 2ADT i with-sem semantics

semantics (2ADTAsset a) _  = VLLeaf.elim-leaf ℕ VLLeaf.Leaf∈ₛGrulerVariant a
semantics (2ADTChoice chc) = BinaryChoice-Semantics GrulerVariant ℕ id 2ADTVL chc
