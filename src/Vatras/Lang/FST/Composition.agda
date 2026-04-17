open import Vatras.Framework.Definitions using (𝔽; 𝔸)
module Vatras.Lang.FST.Composition (F : 𝔽) (A : 𝔸) where

open import Data.List as List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

import Vatras.Util.List as List
import Vatras.Lang.FST
open Vatras.Lang.FST.Impose F A

⊛-all-unique
  : (fs : List FSF)
  → Unique (List.concatMap forget-uniqueness fs)
  → forget-uniqueness (⊛-all fs) ≡ List.concatMap forget-uniqueness fs
⊛-all-unique [] unique-fs = refl
⊛-all-unique (f ∷ fs) unique-fs =
    forget-uniqueness (⊛-all (f ∷ fs))
  ≡⟨⟩
    forget-uniqueness f ⊕ forget-uniqueness (⊛-all fs)
  ≡⟨ Eq.cong (forget-uniqueness f ⊕_) (⊛-all-unique fs (List.AllPairs-++⁻ʳ (forget-uniqueness f) unique-fs)) ⟩
    forget-uniqueness f ⊕ List.concatMap forget-uniqueness fs
  ≡⟨ ⊕-strangers
      (forget-uniqueness f)
      (List.concatMap forget-uniqueness fs)
      (List.AllPairs-++⁻ʳ (forget-uniqueness f) unique-fs)
      (List.AllAll-comm
        (List.concatMap forget-uniqueness fs)
        (forget-uniqueness f)
        ≉-sym
        (List.AllPairs⇒AllAll (forget-uniqueness f) (List.concatMap forget-uniqueness fs) unique-fs))
  ⟩
    forget-uniqueness f ++ List.concatMap forget-uniqueness fs
  ≡⟨⟩
    List.concatMap forget-uniqueness (f ∷ fs)
  ∎
  where
  open Eq.≡-Reasoning
