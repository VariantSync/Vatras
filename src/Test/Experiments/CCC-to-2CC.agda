{-# OPTIONS --sized-types #-}

module Test.Experiments.CCC-to-2CC where

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

open import Framework.Annotation.Name using (Dimension)
-- open import Lang.CCC
--   renaming (Configuration to Configurationₙ;
--             ⟦_⟧ to ⟦_⟧ₙ)
-- open import Lang.2CC
--   renaming (Configuration to Configuration₂;
--             ⟦_⟧ to ⟦_⟧₂)

-- open import Framework.Definitions using (ℂ)
-- open import Translation.CCC-to-2CC  using (CCC→2CC)
-- open import Framework.Proof.Translation using (expr; conf; fnoc)

-- open import Util.ShowHelpers

-- open import Test.Example
-- open import Test.Experiment
-- open import Test.UnitTest

-- open import Util.Named
-- open import Show.Eval

-- open import Test.Examples.CCC

-- -- Make a configuration that always selects n and also generate its name.
-- all-n : ℕ → Named Configurationₙ
-- all-n n = (λ _ → n) called ("all-" ++ show-nat n)

-- CCC→2CC-Test : UnitTest ℕ
-- CCC→2CC-Test n = ForAllExamplesIn cccex-all (test-translation CCC→2CC (get (all-n n)))

-- CCC→2CC-Test-fnoc∘conf : UnitTest ℕ
-- CCC→2CC-Test-fnoc∘conf n = ForAllExamplesIn cccex-all (test-translation-fnoc∘conf≡id CCC→2CC (get (all-n n)))

-- CCC→2CC-Test-all0 : RunTest CCC→2CC-Test 0
-- CCC→2CC-Test-all0 = refl ∷ (refl ∷ (refl ∷ (refl ∷ (refl ∷ (refl ∷ [])))))

-- CCC→2CC-Test-all1 : RunTest CCC→2CC-Test 1
-- CCC→2CC-Test-all1 = refl ∷ (refl ∷ (refl ∷ (refl ∷ (refl ∷ (refl ∷ [])))))

-- CCC→2CC-Test-fnoc∘conf-all0 : RunTest CCC→2CC-Test-fnoc∘conf 0
-- CCC→2CC-Test-fnoc∘conf-all0 = refl ∷ (refl ∷ (refl ∷ (refl ∷ (refl ∷ (refl ∷ [])))))

-- CCC→2CC-Test-fnoc∘conf-all1 : RunTest CCC→2CC-Test-fnoc∘conf 1
-- CCC→2CC-Test-fnoc∘conf-all1 = refl ∷ (refl ∷ (refl ∷ (refl ∷ (refl ∷ (refl ∷ [])))))

-- -- Print all values of a configuration for a list of given dimensions:
-- show-nary-config : Configurationₙ → List Dimension → String
-- show-nary-config = show-fun {Dimension} {ℕ} id show-nat

-- show-binary-config : Configuration₂ → List Dimension → String
-- show-binary-config = show-fun {Dimension} {Bool} id show-bool

-- -- Convert a given named choice calculus formula to binary normal form and back and print all intermediate results.
-- -- Do so for two configurations, one configuration that always selects 0, and one that always selects 1.
-- exp-to-binary-and-back : Experiment (CCC ∞ String)
-- getName exp-to-binary-and-back = "CCC to 2CC and back"
-- get     exp-to-binary-and-back ex@(cc called name) =
--   let
--     conf-vals : List ℕ
--     conf-vals = 0 ∷ 1 ∷ 2 ∷ []

--     translation-result = CCC→2CC cc

--     expr-named : Named (2CC ∞ String)
--     expr-named = expr translation-result called "toCC₂ " ++ name

--     conf-named : Named Configurationₙ → Named Configuration₂
--     conf-named c = (conf translation-result (get c)) called ("(toCC₂ " ++ getName c ++ ")")

--     fnoc-named : Named Configuration₂ → Named Configurationₙ
--     fnoc-named c = (fnoc translation-result (get c)) called ("(toCCₙ " ++ getName c ++ ")")

--     --- helper functions that show the result of "⟦ e ⟧ c", where e is either our original expression or its translation and c is a configuration that always selects n for a given n ∈ ℕ and that has been translated back and forth.
--     eval-all-n       : ℕ → Lines
--     eval-all-n         n = show-eval-str ⟦_⟧ₙ (all-n n) ex
--     eval-forth-all-n : ℕ → Lines
--     eval-forth-all-n   n = show-eval-str ⟦_⟧₂ (conf-named (all-n n)) expr-named
--     eval-back-all-n  : ℕ → Lines
--     eval-back-all-n    n = show-eval-str ⟦_⟧ₙ (fnoc-named (conf-named (all-n n))) ex

--     --- Helper functions to show the configurations mentioned above.
--     show-all-n           : ℕ  → String
--     show-all-n           = λ n → show-named (λ c → show-nary-config   c (Lang.CCC.dims              cc))                          (all-n n)
--     show-conf-all-n      : ℕ  → String
--     show-conf-all-n      = λ n → show-named (λ c → show-binary-config c (Lang.2CC.dims (get expr-named)))             (conf-named (all-n n))
--     show-fnoc-conf-all-n : ℕ  → String
--     show-fnoc-conf-all-n = λ n → show-named (λ c → show-nary-config   c (Lang.CCC.dims              cc))  (fnoc-named (conf-named (all-n n)))
--   in do
--     > show-named Lang.CCC.show ex
--     >∷ mapl (show-all-n) conf-vals
--     lines (mapl eval-all-n conf-vals)
--     linebreak

--     > show-named Lang.2CC.show expr-named
--     >∷ mapl (show-conf-all-n) conf-vals
--     lines (mapl eval-forth-all-n conf-vals)
--     linebreak

--     > name ++ " with configurations converted back and forth "
--     >∷ mapl (show-fnoc-conf-all-n) conf-vals
--     lines (mapl eval-back-all-n conf-vals)
