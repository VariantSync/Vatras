{-# OPTIONS --sized-types #-}

module Test.Test where

open import Data.Bool using (Bool)
open import Data.Bool.Show renaming (show to show-bool)
open import Data.String using (String; _++_)
open import Size using (Size)
open import Relation.Binary.Definitions using (DecidableEquality)

open import SemanticDomain
open import Translation.Translation using (Domain; VarLang; ConfLang; Semantics)

open import Show.Lines

show-in-semantics : String → String
show-in-semantics s = "⟦ " ++ s ++ " ⟧"

variants-are-equal : ∀ {i j : Size} {A : Domain}
    {L₁ L₂ : VarLang}
    {C₁ C₂ : ConfLang}
  → Semantics L₁ C₁
  → Semantics L₂ C₂
  → DecidableEquality A
  → C₁
  → C₂
  → L₁ i A
  → L₂ j A
  → Bool
variants-are-equal ⟦_⟧₁ ⟦_⟧₂ domain-eq c₁ c₂ e₁ e₂ = equals domain-eq (⟦ e₁ ⟧₁ c₁) (⟦ e₂ ⟧₂ c₂)

test-confs : ∀ {i j : Size} {A : Domain}
    {L₁ L₂ : VarLang}
    {C₁ C₂ : ConfLang}
  → (A → String)
  → Semantics L₁ C₁
  → Semantics L₂ C₂
  → DecidableEquality A
  → (conf-name : String)
  → C₁
  → C₂
  → (e₁-name : String)
  → (e₂-name : String)
  → L₁ i A
  → L₂ j A
  → Lines
test-confs {i} {j} {A} {L₁} {L₂} {C₁} {C₂} show-val ⟦_⟧₁ ⟦_⟧₂ domain-eq cname c₁ c₂ e₁-name e₂-name e₁ e₂ =
  let shown-sem₁ = show-in-semantics e₁-name ++ " " ++ cname
      shown-sem₂ = show-in-semantics e₂-name ++ " " ++ cname
      variants-equal = variants-are-equal {i} {j} {A} {L₁} {L₂} {C₁} {C₂} ⟦_⟧₁ ⟦_⟧₂ domain-eq c₁ c₂ e₁ e₂
  in do
    > "Checking variant equality for configuration: " ++ cname
    indent 2 do
      > shown-sem₁ ++ " = " ++ (show-variant show-val (⟦ e₁ ⟧₁ c₁))
      > shown-sem₂ ++ " = " ++ (show-variant show-val (⟦ e₂ ⟧₂ c₂))
      > shown-sem₁ ++ " == " ++ shown-sem₂ ++ " ? " ++ (show-bool variants-equal) ++ "!"
