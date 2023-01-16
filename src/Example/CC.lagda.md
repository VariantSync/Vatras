# 

## Options

```agda
--{-# OPTIONS --sized-types #-}
```

## Module

```agda
module Example.CC where
```

## Imports

```agda

```

### Examples

```agda
CCExample : Set
CCExample = String × CC ∞ String -- name and expression

-- some smart constructors
chcA : ∀ {i : Size} {A : Set} → List⁺ (CC i A) → CC (↑ i) A
chcA es = "A" ⟨ es ⟩

chcA-leaves : ∀ {i : Size} {A : Set} → List⁺ A → CC (↑ ↑ i) A
chcA-leaves es = chcA (leaves es)

-- examples

ccex-ekko : CCExample
ccex-ekko = "ekko" , cc_example_walk

ccex-binary : CCExample
ccex-binary = "binary" , "D" ⟨ leaf "left" ∷ leaf "right" ∷ [] ⟩

ccex-binary-nested : CCExample
ccex-binary-nested = "binary-nested" ,
  "A" ⟨ ("A" ⟨ leaf "1" ∷ leaf "2" ∷ [] ⟩) ∷
        ("A" ⟨ leaf "3" ∷ leaf "4" ∷ [] ⟩) ∷ []
      ⟩

ccex-ternary-nested : CCExample
ccex-ternary-nested = "ternary-nested" ,
  chcA ( chcA-leaves ("1" ∷ "2" ∷ "3" ∷ []) ∷
         chcA-leaves ("4" ∷ "5" ∷ "6" ∷ []) ∷
         chcA-leaves ("7" ∷ "8" ∷ "9" ∷ []) ∷ [])

ccex-complex1 : CCExample
ccex-complex1 = "complex1" ,
  "A" ⟨ ("B" ⟨ leaf "1" ∷ leaf "2" ∷ leaf "3" ∷ [] ⟩) ∷
        ("C" ⟨ leaf "c" ∷ [] ⟩) ∷
        ("A" ⟨ leaf "4" ∷
               ("D" ⟨ leaf "left" ∷ leaf "right" ∷ [] ⟩) ∷
               leaf "5" ∷ []
             ⟩) ∷ []
      ⟩

ccex-nametrick : CCExample
ccex-nametrick = "name-trick" ,
  "A" ⟨ ("A.0" ⟨ leaf "A.0-left" ∷ leaf "A.0-right" ∷ [] ⟩) ∷ leaf "x" ∷ [] ⟩

ccex-all : List CCExample
ccex-all =
  ccex-ekko ∷
  ccex-binary ∷
  ccex-binary-nested ∷
  ccex-ternary-nested ∷
  ccex-complex1 ∷
  ccex-nametrick ∷
  []
```

### Print Helper Functions

Extra imports/opening of functions we use for conversion to string of some data structures:
```agda
open Data.String using (unlines; intersperse)
open Data.List using (concatMap) renaming (_++_ to _++l_)
open Function using (id)

open import Util.ShowHelpers
```

Showing choice calculus expressions:
```agda
showCC : ∀ {i : Size} → CC i String → String
showCC (Artifact a []) = a
showCC (Artifact a es@(_ ∷ _)) = a ++ "-<" ++ (Data.List.foldl _++_ "" (mapl showCC es)) ++ ">-"
showCC (D ⟨ es ⟩) = D ++ "<" ++ (Data.String.intersperse ", " (toList (mapl⁺ showCC es))) ++ ">"

showCC₂ : ∀ {i : Size} → CC₂ i String → String
showCC₂ (Artifact₂ a []) = a
showCC₂ (Artifact₂ a es@(_ ∷ _)) = a ++ "-<" ++ (Data.List.foldl _++_ "" (mapl showCC₂ es)) ++ ">-"
showCC₂ (D ⟨ l , r ⟩₂) = D ++ "<" ++ (showCC₂ l) ++ ", " ++ (showCC₂ r) ++ ">"

open SemanticDomains using (showVariant)
```

Helper functions to collect all dimensions within a choice calculus expression. These might give duplicates because we use lists instead of sets for implementation convenience:
```agda
-- get all dimensions used in a CC expression
dims-CC : ∀ {i : Size} {A : Set} → CC i A → List Dimension
dims-CC (Artifact _ es) = concatMap dims-CC es
dims-CC (D ⟨ es ⟩) = D ∷ concatMap dims-CC (toList es)

-- get all dimensions used in a binary CC expression
dims-CC₂ : ∀ {i : Size} {A : Set} → CC₂ i A → List Dimension
dims-CC₂ (Artifact₂ _ es) = concatMap dims-CC₂ es
dims-CC₂ (D ⟨ l , r ⟩₂) = D ∷ (dims-CC₂ l ++l dims-CC₂ r)
```

Print all values of a configuration for a list of given dimensions:
```agda
show-nary-config : Configuration → List Dimension → String
show-nary-config = show-fun {Dimension} {ℕ} id show-nat

show-binary-config : Configuration₂ → List Dimension → String
show-binary-config = show-fun {Dimension} {Bool} id show-bool
```

Make a configuration that always selects n and also generate its name.
```agda
selectₙ : ℕ → Configuration × String
selectₙ n = (λ {_ → n}) , ("(λ d → " ++ (show-nat n) ++ ")")
```

### Conversion of Examples to Binary CC and Back
Convert a given named choice calculus formula to binary normal form and back and print all intermediate results.
Do so for two configurations, one configuration that always selects 0, and one that always selects 1.
```agda
{-
ccex-toBinaryAndBack : CCExample → String
ccex-toBinaryAndBack (name , cc) = unlines (
  let
    configconverter , cc₂ = toCC₂ cc
    n→b = nary→binary configconverter
    b→n = binary→nary configconverter

    evalₙ : Configuration × String → String
    evalₙ = λ { (conf , cname) →
      "[[" ++ name ++ "]] " ++ cname ++ " = "
      ++ (showVariant (⟦ cc ⟧ conf))}

    eval₂ : Configuration × String → String
    eval₂ = λ { (conf , cname) →
      "[[toCC₂ " ++ name ++ "]] " ++ "(n→b " ++ cname ++ ")" ++ " = "
      ++ (showVariant (⟦ cc₂ ⟧₂ (n→b conf)))}

    eval₂ₙ : Configuration × String → String
    eval₂ₙ = λ { (conf , cname) →
      "[[" ++ name ++ "]] " ++ "(b→n (n→b " ++ cname ++ "))" ++ " = "
      ++ (showVariant (⟦ cc ⟧ (b→n (n→b conf))))}

    eval-selectₙ = evalₙ ∘ selectₙ
    eval-select₂ = eval₂ ∘ selectₙ
    eval-select₂ₙ = eval₂ₙ ∘ selectₙ

    show-config-named : (Configuration × String → String × String) → ℕ → String
    show-config-named = λ show-config n →
      let conf-print , name = show-config (selectₙ n)
      in
      name ++ ": " ++ conf-print
    show-selectₙ = show-config-named (λ (conf , name) → show-nary-config conf (dims-CC cc) , name)
    show-select₂ = show-config-named (λ (conf , name) → (show-binary-config ∘ n→b) conf (dims-CC₂ cc₂) , ("n→b " ++ name))
    show-select₂ₙ = show-config-named (λ (conf , name) → (show-nary-config ∘ b→n ∘ n→b) conf (dims-CC cc) , ("b→n (n→b " ++ name ++ ")"))
  in
  ("=== Example: " ++ name ++ " ===") ∷
  (name ++ " = " ++ (showCC cc)) ∷
  (show-selectₙ 0) ∷
  (show-selectₙ 1) ∷
  (show-selectₙ 2) ∷
  (eval-selectₙ 0) ∷
  (eval-selectₙ 1) ∷
  (eval-selectₙ 2) ∷
  ("toCC₂ " ++ name ++ " = " ++ (showCC₂ cc₂)) ∷
  (show-select₂ 0) ∷
  (show-select₂ 1) ∷
  (show-select₂ 2) ∷
  (eval-select₂ 0) ∷
  (eval-select₂ 1) ∷
  (eval-select₂ 2) ∷
  (name ++ " with configurations converted back and forth ") ∷
  (show-select₂ₙ 0) ∷
  (show-select₂ₙ 1) ∷
  (show-select₂ₙ 2) ∷
  (eval-select₂ₙ 0) ∷
  (eval-select₂ₙ 1) ∷
  (eval-select₂ₙ 2) ∷
  []) -}
```

### Final Printing
Print the binary-conversion for all examples:
```agda
--mainStr : String
--mainStr = intersperse "\n\n" (mapl ccex-toBinaryAndBack ccex-all)
```