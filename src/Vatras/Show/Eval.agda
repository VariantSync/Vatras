{-|
Some helper functions for pretty printing.
-}
module Vatras.Show.Eval where

open import Data.Bool using (Bool)
open import Data.Bool.Show renaming (show to show-bool)
open import Data.String using (String; _++_)
open import Size using (Size)
open import Function using (id)

open import Vatras.Framework.Definitions
open import Vatras.Framework.VariabilityLanguage

open import Vatras.Show.Lines
open import Vatras.Util.Named

show-in-semantics : String → String
show-in-semantics s = "⟦ " ++ s ++ " ⟧"

show-eval : ∀ {V A}
  → (L : VariabilityLanguage V)
  → (V A → String)
  → Named (Config L)
  → Named (Expression L A)
  → Lines
show-eval L show-variant (c called cname) (e called ename) =
  > show-in-semantics ename ++ " " ++ cname ++ " = " ++ (show-variant (⟦ e ⟧ c))
  where
    ⟦_⟧ = Semantics L
