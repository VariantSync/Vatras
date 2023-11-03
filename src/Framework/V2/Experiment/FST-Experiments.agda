{-# OPTIONS --allow-unsolved-metas #-}

open import Framework.V2.Definitions
module Framework.V2.Experiment.FST-Experiments where

open import Data.Bool using (true; false)
open import Data.List using (List; _∷_; []; map; [_])
open import Data.Product using (proj₁; proj₂; _,_; _×_)
open import Function using (id)

open import Relation.Binary using (DecidableEquality)
open import Relation.Nullary.Decidable using (yes; no; does; _because_; _×-dec_)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Framework.V2.Lang.FST as FSTModule

open import Util.Named
open import Test.Example
open import Test.Experiment
open import Show.Lines
open import Util.ShowHelpers
open import Data.String using (String; _<+>_; _++_; _≟_)

exp : ∀ {N A}
  → (N → String)
  → (A → String)
  → DecidableEquality A
  → List (Conf N)
  → Experiment (FeatureForest N A)
getName (exp _ _ _ _) = "Configure FST example"
get (exp show-N show-A _≟_ configs) (example-name ≔ forest) =
  let open FSTModule.Show show-N show-A
      open FSTModule.Algebra _≟_
  in
  do
  > "Expression e has features"
  indent 2 do
    lines (map show-Feature forest)

  foreach [ c ∈ configs ] do
    let cstr = show-fun show-N show-bool c (names forest)
    linebreak
    > "⟦ e ⟧" <+> cstr <+> "="
    indent 2 do
      show-FST (⟦ forest ⟧ c)

pick-all : ∀ {N} → Conf N
pick-all _ = true

pick-only : ∀ {N} → DecidableEquality N → N → Conf N
pick-only _==_ n n' = does (n == n')

module Java where
  ASTNode = String

  class = "class" <+>_
  method = "method" <+>_
  return : String → ASTNode
  return e = "return" <+> e ++ ";"

  _≟-ast_ : DecidableEquality ASTNode
  _≟-ast_ = _≟_

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

    feature-Add : Feature String ASTNode
    feature-Add = fname-Add :: cls ． add ． add-ret ． []

    feature-Sub : Feature String ASTNode
    feature-Sub = fname-Sub :: cls ． sub ． sub-ret ． []

    feature-Log : Feature String ASTNode
    feature-Log = fname-Log :: cls ．
      branches (
        (add ． log ． [])
      ∷ (sub ． log ． [])
      ∷ [])

    ---- Example SPLs

    ex-Add-Sub : Example (FeatureForest String ASTNode)
    ex-Add-Sub = "add-sub" ≔ feature-Add ∷ feature-Sub ∷ []

    ex-Sub-Add : Example (FeatureForest String ASTNode)
    ex-Sub-Add = "sub-add" ≔ feature-Sub ∷ feature-Add ∷ []

    ex-Add-Sub-Log : Example (FeatureForest String ASTNode)
    ex-Add-Sub-Log = "add-sub" ≔ feature-Add ∷ feature-Sub ∷ feature-Log ∷ []

    ex-all : List (Example (FeatureForest String ASTNode))
    ex-all = ex-Add-Sub ∷ ex-Sub-Add ∷ ex-Add-Sub-Log ∷ []

    ---- Experiments

    toy-calculator-experiment =
      let eq = _≟-ast_ in
      exp id id eq (pick-all ∷ pick-only eq fname-Add ∷ [])
