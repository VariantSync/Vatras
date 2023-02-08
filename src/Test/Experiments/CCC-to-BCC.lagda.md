# Test Cases for Converting Core to Binary Choice Calculus

## Options

```agda
{-# OPTIONS --sized-types #-}
```

## Module

```agda
module Test.Experiments.CCC-to-BCC where
```

## Imports

```agda
open import Data.Bool
  using (Bool)
open import Data.List
  using (List; []; _∷_; lookup; concatMap)
  renaming (map to mapl; _++_ to _++l_)
open import Data.Nat
  using (ℕ)
open import Data.Nat.Show
  renaming (show to show-nat)
open import Data.Product
  using (_,_; _×_)
open import Data.String
  using (String; _++_; intersperse)
open import Function
  using (_∘_; id)
open import Size using (∞)

open import Show.Lines

open import Lang.Annotation.Name using (Dimension)
open import Lang.CCC
  renaming (Configuration to Configurationₙ;
            ⟦_⟧ to ⟦_⟧ₙ)
open import Lang.BCC
  renaming (Configuration to Configuration₂;
            ⟦_⟧ to ⟦_⟧₂)

open import SemanticDomain using (show-variant)

open import Translation.CCC-to-BCC  using (CCC→BCC)
open import Translation.Translation using (translate; expr; conf; fnoc)

open import Util.ShowHelpers

open import Test.Example
open import Test.Experiment
```

## Print Helper Functions

Print all values of a configuration for a list of given dimensions:
```agda
show-nary-config : Configurationₙ → List Dimension → String
show-nary-config = show-fun {Dimension} {ℕ} id show-nat

show-binary-config : Configuration₂ → List Dimension → String
show-binary-config = show-fun {Dimension} {Bool} id show-bool
```

Make a configuration that always selects n and also generate its name.
```agda
selectₙ : ℕ → Configurationₙ × String
selectₙ n = (λ {_ → n}) , ("(λ d → " ++ (show-nat n) ++ ")")
```

### Conversion of Examples to Binary CC and Back
Convert a given named choice calculus formula to binary normal form and back and print all intermediate results.
Do so for two configurations, one configuration that always selects 0, and one that always selects 1.
```agda
exp-to-binary-and-back : Experiment (CCC ∞ String)
name exp-to-binary-and-back = "CCC to BCC and back"
run  exp-to-binary-and-back (name example: cc) =
  let
    translation-result = translate CCC→BCC cc
    cc₂ = expr translation-result
    n→b = conf translation-result
    b→n = fnoc translation-result

    evalₙ : Configurationₙ × String → String
    evalₙ = λ { (conf , cname) →
      "[[" ++ name ++ "]] " ++ cname ++ " = "
      ++ (show-variant id (⟦ cc ⟧ₙ conf))}

    eval₂ : Configurationₙ × String → String
    eval₂ = λ { (conf , cname) →
      "[[toBCC " ++ name ++ "]] " ++ "(n→b " ++ cname ++ ")" ++ " = "
      ++ (show-variant id (⟦ cc₂ ⟧₂ (n→b conf)))}

    eval₂ₙ : Configurationₙ × String → String
    eval₂ₙ = λ { (conf , cname) →
      "[[" ++ name ++ "]] " ++ "(b→n (n→b " ++ cname ++ "))" ++ " = "
      ++ (show-variant id (⟦ cc ⟧ₙ (b→n (n→b conf))))}

    eval-selectₙ = evalₙ ∘ selectₙ
    eval-select₂ = eval₂ ∘ selectₙ
    eval-select₂ₙ = eval₂ₙ ∘ selectₙ

    show-config-named : (Configurationₙ × String → String × String) → ℕ → String
    show-config-named = λ show-config n →
      let conf-print , name = show-config (selectₙ n)
      in
      name ++ ": " ++ conf-print
    show-selectₙ = show-config-named (λ (conf , name) → show-nary-config conf (Lang.CCC.dims cc) , name)
    show-select₂ = show-config-named (λ (conf , name) → (show-binary-config ∘ n→b) conf (Lang.BCC.dims cc₂) , ("n→b " ++ name))
    show-select₂ₙ = show-config-named (λ (conf , name) → (show-nary-config ∘ b→n ∘ n→b) conf (Lang.CCC.dims cc) , ("b→n (n→b " ++ name ++ ")"))
  in do
  > name ++ " = " ++ (Lang.CCC.show cc)
  > show-selectₙ 0
  > show-selectₙ 1
  > show-selectₙ 2
  > eval-selectₙ 0
  > eval-selectₙ 1
  > eval-selectₙ 2
  > "toCC₂ " ++ name ++ " = " ++ (Lang.BCC.show cc₂)
  > show-select₂ 0
  > show-select₂ 1
  > show-select₂ 2
  > eval-select₂ 0
  > eval-select₂ 1
  > eval-select₂ 2
  > name ++ " with configurations converted back and forth "
  > show-select₂ₙ 0
  > show-select₂ₙ 1
  > show-select₂ₙ 2
  > eval-select₂ₙ 0
  > eval-select₂ₙ 1
  > eval-select₂ₙ 2
```

