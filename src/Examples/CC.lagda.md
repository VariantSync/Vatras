# Examples of Core and Binary Choice Calculus

## Options

```agda
{-# OPTIONS --sized-types #-}
```

## Module

```agda
module Examples.CC where
```

## Imports

```agda
-- stdlib
open import Data.Bool
  using (Bool)
open import Data.List
  using (List; []; _∷_; lookup; concatMap)
  renaming (map to mapl; _++_ to _++l_)
open import Data.List.NonEmpty
  using (List⁺; _∷_; toList)
  renaming (map to mapl⁺)
open import Data.Nat
  using (ℕ)
open import Data.Nat.Show
  renaming (show to show-nat)
open import Data.Product
  using (_,_; _×_)
open import Data.String
  using (String; _++_; unlines; intersperse)
open import Function
  using (_∘_; id)
open import Size
  using (Size; ∞; ↑_)

-- own modules
open import Lang.Annotation.Dimension using (Dimension)
open import SemanticDomain using (showVariant)
open import Lang.CCC
  renaming (Configuration to Configurationₙ;
            ⟦_⟧ to ⟦_⟧ₙ)
open import Lang.BCC
  renaming (Configuration to Configuration₂;
            ⟦_⟧ to ⟦_⟧₂)

open import Translation.CCC-to-BCC

open import Util.ShowHelpers
```

### Examples

```agda
CCExample : Set
CCExample = String × CCC ∞ String -- name and expression

-- some smart constructors
chcA : ∀ {i : Size} {A : Set} → List⁺ (CCC i A) → CCC (↑ i) A
chcA es = "A" ⟨ es ⟩

chcA-leaves : ∀ {i : Size} {A : Set} → List⁺ A → CCC (↑ ↑ i) A
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
ccex-toBinaryAndBack : CCExample → String
ccex-toBinaryAndBack (name , cc) = unlines (
  let
    configconverter , cc₂ = toBCC cc
    n→b = nary→binary configconverter
    b→n = binary→nary configconverter

    evalₙ : Configurationₙ × String → String
    evalₙ = λ { (conf , cname) →
      "[[" ++ name ++ "]] " ++ cname ++ " = "
      ++ (showVariant (⟦ cc ⟧ₙ conf))}

    eval₂ : Configurationₙ × String → String
    eval₂ = λ { (conf , cname) →
      "[[toBCC " ++ name ++ "]] " ++ "(n→b " ++ cname ++ ")" ++ " = "
      ++ (showVariant (⟦ cc₂ ⟧₂ (n→b conf)))}

    eval₂ₙ : Configurationₙ × String → String
    eval₂ₙ = λ { (conf , cname) →
      "[[" ++ name ++ "]] " ++ "(b→n (n→b " ++ cname ++ "))" ++ " = "
      ++ (showVariant (⟦ cc ⟧ₙ (b→n (n→b conf))))}

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
  in
  ("=== Example: " ++ name ++ " ===") ∷
  (name ++ " = " ++ (Lang.CCC.show cc)) ∷
  (show-selectₙ 0) ∷
  (show-selectₙ 1) ∷
  (show-selectₙ 2) ∷
  (eval-selectₙ 0) ∷
  (eval-selectₙ 1) ∷
  (eval-selectₙ 2) ∷
  ("toCC₂ " ++ name ++ " = " ++ (Lang.BCC.show cc₂)) ∷
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
  [])
```

### Final Printing
Print the binary-conversion for all examples:
```agda
mainStr : String
mainStr = intersperse "\n\n" (mapl ccex-toBinaryAndBack ccex-all)
```
