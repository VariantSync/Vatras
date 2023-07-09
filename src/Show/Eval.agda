{-# OPTIONS --sized-types #-}

module Show.Eval where

open import Data.Bool using (Bool)
open import Data.Bool.Show renaming (show to show-bool)
open import Data.String using (String; _++_)
open import Size using (Size)
open import Function using (id)

open import Framework.Definitions using (𝔸; 𝕃; ℂ; Semantics; show-variant)

open import Show.Lines
open import Util.Named

show-in-semantics : String → String
show-in-semantics s = "⟦ " ++ s ++ " ⟧"

show-eval : ∀ {i : Size} {A : 𝔸} {L : 𝕃} {C : ℂ}
  → (A → String)
  → Semantics L C
  → Named C
  → Named (L i A)
  → Lines
show-eval show-val ⟦_⟧ (c called cname) (e called ename) =
  > show-in-semantics ename ++ " " ++ cname ++ " = " ++ (show-variant show-val (⟦ e ⟧ c))

show-eval-str : ∀ {i : Size} {L : 𝕃} {C : ℂ}
  → Semantics L C
  → Named C
  → Named (L i String)
  → Lines
show-eval-str {i} {L} {C} = show-eval {i} {String} {L} {C} id
