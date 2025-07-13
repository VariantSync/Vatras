open import Vatras.Framework.Definitions
module Vatras.Test.Experiments.FST-Experiments where

open import Data.Bool using (true; false)
open import Data.List using (List; _∷_; []; map; [_])
open import Data.Product using (proj₁; proj₂; _,_; _×_)
open import Function using (id; _∘_)

open import Relation.Binary using (DecidableEquality)
open import Relation.Nullary.Decidable using (yes; no; does; _because_; _×-dec_)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Vatras.Util.Named
open import Vatras.Test.Example
open import Vatras.Test.Experiment
open import Vatras.Show.Lines hiding (map)
open import Vatras.Util.ShowHelpers
open import Data.String as String using (String; _<+>_; _++_) renaming (_≟_ to _≟ˢ_)

open import Vatras.Framework.Variants using (show-rose)

open import Vatras.Lang.All
open FST using (Configuration)

module _ (F : 𝔽) (A : 𝔸) where
-- (_≟_ : DecidableEquality A)
  open FST.Impose {F} A
  module FSTShow = FST.Impose.Show {F} A

  exp :
      (F → String)
    → (atoms A → String)
    → List (Configuration F)
    → Experiment SPL
  getName (exp _ _ _) = "Configuration FST example"
  get (exp show-N show-A configs) (example-name ≔ forest) =
    let open FSTShow show-N show-A
    in
    do
    > "Expression e has features"
    indent 2 do
      lines (map show-Feature (features forest))

    foreach [ c ∈ configs ] do
      let cstr = show-fun show-N show-bool c (names forest)
      linebreak
      > "⟦ e ⟧" <+> cstr <+> "="
      indent 2 do
        > show-rose show-A (⟦ forest ⟧ c)

pick-all : ∀ {N} → Configuration N
pick-all _ = true

pick-only : ∀ {N} → DecidableEquality N → N → Configuration N
pick-only _==_ n n' = does (n == n')

module Java where
  ASTNode = String

  class = "class" <+>_
  method = "method" <+>_
  return : String → ASTNode
  return e = "return" <+> e ++ ";"

  _≟-ast_ : DecidableEquality ASTNode
  _≟-ast_ = _≟ˢ_

  A : 𝔸
  A = record
    { atoms = ASTNode
    ; atomsEqual? = _≟-ast_
    }
  open FST.Impose {String} A

  module Calculator where
    fname-Add = "Add"
    fname-Sub = "Sub"
    fname-Log = "Log"

    cls = class "Calculator"

    add = method "add(int,int)"
    add-ret = return "x + y"

    sub = method "sub(int,int)"
    sub-ret = return "x - y"

    log = "log(x + \", \" + y);"

    ---- Features

    open import Data.Unit using (tt)
    open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
    open import Data.List.Relation.Unary.All using ([]; _∷_)

    feature-Add : Feature
    feature-Add = fname-Add :: (cls ． add ． add-ret ． []) ⊚ (([] ∷ []) , ((([] ∷ []) , ((([] ∷ []) , (([] , []) ∷ [])) ∷ [])) ∷ []))

    feature-Sub : Feature
    feature-Sub = fname-Sub :: (cls ． sub ． sub-ret ． []) ⊚ (([] ∷ []) , ((([] ∷ [] , ((([] ∷ []) , ((([] , [])) ∷ []))) ∷ [])) ∷ []))

    feature-Log : Feature
    feature-Log = fname-Log :: (cls ．
      branches (
        (add ． log ． [])
      ∷ (sub ． log ． [])
      ∷ [])) ⊚ (([] ∷ []) , ((((((λ where ()) ∷ []) ∷ ([] ∷ [])) , (((([] ∷ []) , ((([] , [])) ∷ []))) ∷ (((([] ∷ []) , ((([] , [])) ∷ []))) ∷ [])))) ∷ []))

    ---- Example SPLs

    ex-Add-Sub : Example SPL
    ex-Add-Sub = "add-sub" ≔ "package" ◀ (feature-Add ∷ feature-Sub ∷ [])

    ex-Sub-Add : Example SPL
    ex-Sub-Add = "sub-add" ≔ "package" ◀ (feature-Sub ∷ feature-Add ∷ [])

    ex-Add-Sub-Log : Example SPL
    ex-Add-Sub-Log = "add-sub" ≔ "package" ◀ (feature-Add ∷ feature-Sub ∷ feature-Log ∷ [])

    ex-all : List (Example SPL)
    ex-all = ex-Add-Sub ∷ ex-Sub-Add ∷ ex-Add-Sub-Log ∷ []

    ---- Experiments

    toy-calculator-experiment =
      let eq = _≟-ast_ in
      exp String A id id (pick-all ∷ pick-only eq fname-Add ∷ [])
