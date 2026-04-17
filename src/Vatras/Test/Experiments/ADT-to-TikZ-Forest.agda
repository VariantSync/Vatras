open import Vatras.Framework.Definitions
module Vatras.Test.Experiments.ADT-to-TikZ-Forest where

open import Data.List as List using ([]; _∷_)
open import Data.Product using (_,_; proj₁)
open import Data.String as String using (String; _++_; intersperse)

open import Size using (∞)
open import Function using (id)

open import Vatras.Framework.Variants
open import Vatras.Lang.All
open CCC using (CCC)
open 2CC using (2CC)
open ADT using (ADT; leaf; _⟨_,_⟩)
open import Vatras.Translation.LanguageMap
open import Vatras.Translation.Lang.2CC.Idempotence String String._≟_ using (eliminate-idempotent-choices)

import Vatras.Lang.CCC.Show as CCCShow

open import Vatras.Test.Experiment
open import Vatras.Show.Lines
open import Vatras.Util.Named

STRCCC = CCC String ∞ STRING
STR2CC = 2CC String ∞ STRING
STRADT = ADT String (Rose ∞) STRING

rose-to-tikz-forest : ∀ {i} {A : 𝔸} → (atoms A → String) → Rose i A → Lines
rose-to-tikz-forest pretty-atom (a -< [] >-) = > "[" ++ pretty-atom a ++ "]"
rose-to-tikz-forest pretty-atom (a -< cs@(_ ∷ _) >-) = do
  > "[" ++ pretty-atom a
  indent 2 do
    lines (List.map (rose-to-tikz-forest pretty-atom) cs)
  > "]"

adt-to-tikz-forest : ∀ {A : 𝔸} → {V : 𝕍} → {F : 𝔽} → (V A → Lines) → (F → String) → ADT F V A → Lines
adt-to-tikz-forest pretty-variant show-F (leaf v) = pretty-variant v
adt-to-tikz-forest pretty-variant show-F (D ⟨ l , r ⟩) = do
  > "[" ++ show-F D
  indent 2 do
    adt-to-tikz-forest pretty-variant show-F l
    adt-to-tikz-forest pretty-variant show-F r
  > "]"

CCC-to-ADT : STRCCC → STRADT
CCC-to-ADT ccc = adt
  where
    open Expressiveness-String

    bcc : STR2CC
    bcc = proj₁ (2CC≽CCC ccc)

    bcc' : STR2CC
    bcc' = eliminate-idempotent-choices bcc

    adt : STRADT
    adt = proj₁ (ADT≽2CC bcc')

tikz-export-experiment : Experiment STRCCC
getName tikz-export-experiment = "Tikz-Export"
get tikz-export-experiment (ccc called name) = do
  [ Center ]> "Input CCC expression:"
  linebreak
  CCCShow.pretty id ccc
  linebreak
  [ Center ]> "Tikz export of corresponding ADT:"
  linebreak
  let adt = CCC-to-ADT ccc
  adt-to-tikz-forest (rose-to-tikz-forest λ a → "$" ++ a ++ "$") id adt
