{-# OPTIONS --allow-unsolved-metas #-}
{-# OPTIONS --sized-types #-}

open import Framework.Definitions
module Test.Experiments.FST-Experiments where

open import Data.Bool using (true; false)
open import Data.List using (List; _∷_; []; map; [_])
open import Data.Product using (proj₁; proj₂; _,_; _×_)
open import Function using (id)

open import Relation.Binary using (DecidableEquality)
open import Relation.Nullary.Decidable using (yes; no; does; _because_; _×-dec_)

open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Util.Named
open import Test.Example
open import Test.Experiment
open import Show.Lines
open import Util.ShowHelpers
open import Data.String using (String; _<+>_; _++_) renaming (_≟_ to _≟ˢ_)

open import Lang.FST as FSTModule using (Conf)

module _ {A : 𝔸} (_≟_ : DecidableEquality A) where
  open FSTModule.Defs {A}
  open FSTModule.Defs.Impose _≟_
  module FSTShow = FSTModule.Defs.Impose.Show

  exp : ∀ {N}
    → (N → String)
    → (A → String)
    → List (Conf N)
    → Experiment (SPL N)
  getName (exp _ _ _) = "Configure FST example"
  get (exp show-N show-A configs) (example-name ≔ forest) =
    let open FSTShow _≟_ show-N show-A
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
        show-FSF (forget-uniqueness (⟦ forest ⟧ c))

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
  _≟-ast_ = _≟ˢ_

  open FSTModule.Defs {ASTNode}
  open FSTModule.Defs.Impose _≟-ast_

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

    feature-Add : Feature ASTNode
    feature-Add = fname-Add :: (cls ． add ． add-ret ． [] , ([] ∷ []) , ((unq ([] ∷ [] , (unq (([] ∷ []) , ((unq ([] , [])) ∷ []))) ∷ [])) ∷ []))

    feature-Sub : Feature ASTNode
    feature-Sub = fname-Sub :: (cls ． sub ． sub-ret ． [] , ([] ∷ []) , ((unq ([] ∷ [] , (unq (([] ∷ []) , ((unq ([] , [])) ∷ []))) ∷ [])) ∷ []))

    feature-Log : Feature ASTNode
    feature-Log = fname-Log :: cls ．
      branches (
        (add ． log ． [])
      ∷ (sub ． log ． [])
      ∷ []) , ([] ∷ []) , ((unq (((tt ∷ []) ∷ ([] ∷ [])) , ((unq (([] ∷ []) , ((unq ([] , [])) ∷ []))) ∷ ((unq (([] ∷ []) , ((unq ([] , [])) ∷ []))) ∷ [])))) ∷ [])

    ---- Example SPLs

    ex-Add-Sub : Example (SPL ASTNode)
    ex-Add-Sub = "add-sub" ≔ feature-Add ∷ feature-Sub ∷ []

    ex-Sub-Add : Example (SPL ASTNode)
    ex-Sub-Add = "sub-add" ≔ feature-Sub ∷ feature-Add ∷ []

    ex-Add-Sub-Log : Example (SPL ASTNode)
    ex-Add-Sub-Log = "add-sub" ≔ feature-Add ∷ feature-Sub ∷ feature-Log ∷ []

    ex-all : List (Example (SPL ASTNode))
    ex-all = ex-Add-Sub ∷ ex-Sub-Add ∷ ex-Add-Sub-Log ∷ []

    ---- Experiments

    toy-calculator-experiment =
      let eq = _≟-ast_ in
      exp eq id id (pick-all ∷ pick-only eq fname-Add ∷ [])
