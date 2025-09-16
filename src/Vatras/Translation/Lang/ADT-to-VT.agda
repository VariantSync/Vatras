{-|
Algebraic decision trees are a normal form of variation trees.
Hence translating algebraic decision trees to variation trees is trivial.
-}
open import Vatras.Framework.Definitions using (𝔽)
module Vatras.Translation.Lang.ADT-to-VT (F : 𝔽) where

open import Data.Bool using (if_then_else_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≗_)
open Eq.≡-Reasoning

open import Vatras.Data.Prop using (Prop; eval)
open import Vatras.Data.EqIndexedSet using (≗→≅[])
open import Vatras.Framework.Variants using (Forest)
open import Vatras.Framework.Compiler using (_⊕_; LanguageCompiler)

open import Vatras.Lang.ADT F Forest using (ADTL)
open import Vatras.Lang.ADT.Prop F Forest
open import Vatras.Lang.VT F as VT
open import Vatras.Lang.VT.Encode F using (encode-forest; encode-forest-preserves)

open import Vatras.Framework.Relation.Expressiveness Forest using (_≽_; expressiveness-from-compiler)
open import Vatras.Translation.Lang.ADT.ADT-vs-PropADT F Forest using (lift-compiler; ADT≽PropADT)

open import Vatras.Util.AuxProofs using (if-cong)

translate' : ∀ {A} → PropADT A → List (UnrootedVT A)
translate' (leaf v)      = encode-forest v
translate' (D ⟨ l , r ⟩) = if[ D ]then[ translate' l ]else[ translate' r ] ∷ []

translate : ∀ {A} → PropADT A → VT A
translate e = if-true[ translate' e ]

preserves : ∀ {A} → (e : PropADT A) → ⟦ e ⟧ₚ ≗ ⟦ translate e ⟧
preserves (leaf v) c      = Eq.sym (encode-forest-preserves v c)
preserves (D ⟨ l , r ⟩) c =
    ⟦ D ⟨ l , r ⟩ ⟧ₚ c
  ≡⟨⟩
    (if eval D c then ⟦ l ⟧ₚ c else ⟦ r ⟧ₚ c)
  ≡⟨ if-cong (eval D c) (preserves l c) (preserves r c) ⟩
    (if eval D c then configure-all (translate' l) c else configure-all (translate' r) c)
  ≡⟨ ++-identityʳ _ ⟨
    (if eval D c then configure-all (translate' l) c else configure-all (translate' r) c) ++ []
  ≡⟨⟩
    configure-all (if[ D ]then[ translate' l ]else[ translate' r ] ∷ []) c
  ≡⟨⟩
    configure-all (translate' (D ⟨ l , r ⟩)) c
  ∎

PropADT→VT : LanguageCompiler PropADTL VTL
PropADT→VT = record
  { compile = translate
  ; config-compiler = λ e → record { to = id ; from = id }
  ; preserves = ≗→≅[] ∘ preserves
  }

VT≽PropADT : VTL ≽ PropADTL
VT≽PropADT = expressiveness-from-compiler PropADT→VT

ADT→VT : LanguageCompiler ADTL VTL
ADT→VT = lift-compiler ⊕ PropADT→VT

VT≽ADT : VTL ≽ ADTL
VT≽ADT = expressiveness-from-compiler ADT→VT
