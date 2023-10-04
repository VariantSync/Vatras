module Framework.V2.Lang.2ADT where

open import Data.Bool using (Bool)
open import Data.Nat using (ℕ)

open import Framework.V2.Definitions
open import Framework.V2.Constructs.GrulerArtifacts
open import Framework.V2.Constructs.Choices
open import Framework.V2.Variants using (GrulerVariant)

private
  variable
    A : 𝔸

  BinaryChoice = VLChoice₂.Syntax
  BinaryChoice-Semantics = VLChoice₂.Semantics

data 2ADT : 𝔼 where
  2ADTAsset  : Leaf A                → 2ADT A
  2ADTChoice : BinaryChoice ℕ 2ADT A → 2ADT A

{-# TERMINATING #-}
⟦_⟧-2adt : 𝔼-Semantics GrulerVariant ℕ Bool 2ADT

2ADTVL : VariabilityLanguage GrulerVariant ℕ Bool
expression-set 2ADTVL = 2ADT
semantics 2ADTVL   = ⟦_⟧-2adt

⟦ 2ADTAsset A  ⟧-2adt = VLLeaf.Semantics VLLeaf.Leaf∈ₛGrulerVariant 2ADTVL A
⟦ 2ADTChoice C ⟧-2adt = BinaryChoice-Semantics 2ADTVL C
