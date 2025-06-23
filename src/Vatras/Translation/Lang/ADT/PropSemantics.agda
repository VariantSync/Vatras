open import Vatras.Framework.Definitions using (𝔽; 𝕍; 𝔸)
module Vatras.Translation.Lang.ADT.PropSemantics (F : 𝔽) (V : 𝕍) where

open import Data.Bool using (true; false; if_then_else_; not) renaming (_∧_ to _and_)
open import Data.Product using (_,_)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl)
open Eq.≡-Reasoning

import Vatras.Lang.ADT
module ADT F = Vatras.Lang.ADT F V
open ADT hiding (⟦_⟧)
⟦_⟧ = ADT.⟦_⟧ F

open import Vatras.Data.EqIndexedSet using (≗→≅[])
open import Vatras.Data.Prop
open import Vatras.Lang.ADT.Prop F V
open import Vatras.Util.AuxProofs using (if-flip; if-∧; if-cong; if-congˡ)
open import Vatras.Framework.Compiler
open import Vatras.Framework.Relation.Expressiveness V using (_≽_; expressiveness-from-compiler)

{-|
Elimination of formulas in choices.
The elimination uses the transformation rules of the formula choice calculus.
We use this auxiliary function solely for termination checking.
Note that this function is actually independent of ADTs, so we can potentially generalize it to choices for any language.
All it takes is a choice constructor.
-}
↓_⟨_,_⟩ : ∀ {A} → Prop F → ADT F A → ADT F A → ADT F A
↓ true  ⟨ l , _ ⟩ = l
↓ false ⟨ _ , r ⟩ = r
↓ var X ⟨ l , r ⟩ = X ⟨ l , r ⟩
↓ ¬ P   ⟨ l , r ⟩ = ↓ P ⟨ r , l ⟩
↓ P ∧ Q ⟨ l , r ⟩ = ↓ P ⟨ ↓ Q ⟨ l , r ⟩ , r ⟩

elim-formulas : ∀ {A} → ADT (Prop F) A → ADT F A
elim-formulas (leaf v)      = leaf v
elim-formulas (P ⟨ l , r ⟩) = ↓ P ⟨ elim-formulas l , elim-formulas r ⟩

---- Preservation Proofs ----

{-|
Intermediary semantics for choices whose formulas are about to be eliminated.
The alternatives are already transformed.
We need this intermediary semantics to convince the termination checker that our proof uses
well-founded induction.
-}
elim-sem : ∀ {A} → Prop F → (l r : ADT F A) → Configuration F → V A
elim-sem P l r c = if eval P c then ⟦ l ⟧ c else ⟦ r ⟧ c

↓-presʳ : ∀ {A} (P : Prop F) (l r : ADT F A)
  → elim-sem P l r ≗ ⟦ ↓ P ⟨ l , r ⟩ ⟧
↓-presʳ true    l r c = refl
↓-presʳ false   l r c = refl
↓-presʳ (var x) l r c = refl
↓-presʳ (¬ P)   l r c =
    elim-sem (¬ P) l r c
  ≡⟨⟩
    (if not (eval P c) then ⟦ l ⟧ c else ⟦ r ⟧ c)
  ≡⟨ if-flip (eval P c) _ _ ⟩
    (if eval P c then ⟦ r ⟧ c else ⟦ l ⟧ c)
  ≡⟨⟩
    elim-sem P r l c
  ≡⟨ ↓-presʳ P r l c ⟩
    ⟦ ↓ P ⟨ r , l ⟩ ⟧ c
  ≡⟨⟩
    ⟦ ↓ (¬ P) ⟨ l , r ⟩ ⟧ c
  ∎
↓-presʳ (P ∧ Q) l r c =
    elim-sem (P ∧ Q) l r c
  ≡⟨⟩
    (if eval P c and eval Q c then ⟦ l ⟧ c else ⟦ r ⟧ c)
  ≡⟨ if-∧ (eval P c) (eval Q c) _ _ ⟩
    (if eval P c then (if eval Q c then ⟦ l ⟧ c else ⟦ r ⟧ c) else ⟦ r ⟧ c)
  ≡⟨⟩
    (if eval P c then elim-sem Q l r c else ⟦ r ⟧ c)
  ≡⟨ if-congˡ (eval P c) (↓-presʳ Q l r c) ⟩
    (if eval P c then ⟦ ↓ Q ⟨ l , r ⟩ ⟧ c else ⟦ r ⟧ c)
  ≡⟨⟩
    elim-sem P ↓ Q ⟨ l , r ⟩ r c
  ≡⟨ ↓-presʳ P (↓ Q ⟨ l , r ⟩) r c ⟩
    ⟦ ↓ P ⟨ ↓ Q ⟨ l , r ⟩ , r ⟩ ⟧ c
  ∎

mutual
  ↓-presˡ : ∀ {A} (P : Prop F) (l r : ADT (Prop F) A)
    → ⟦ P ⟨ l , r ⟩ ⟧ₚ ≗ elim-sem P (elim-formulas l) (elim-formulas r)
  ↓-presˡ true    l r c = preserves l c
  ↓-presˡ false   l r c = preserves r c
  ↓-presˡ (var x) l r c = if-cong _ (preserves l c) (preserves r c)
  ↓-presˡ (¬ P)   l r c = if-cong _ (preserves l c) (preserves r c)
  ↓-presˡ (P ∧ Q) l r c = if-cong _ (preserves l c) (preserves r c)

  preserves
    : ∀ {A}
    → (e : ADT (Prop F) A)
    → ⟦ e ⟧ₚ ≗ ⟦ elim-formulas e ⟧
  preserves (leaf _) _ = refl
  preserves (D ⟨ l , r ⟩) c =
      ⟦ D ⟨ l , r ⟩ ⟧ₚ c
    ≡⟨ ↓-presˡ D l r c ⟩
      elim-sem D (elim-formulas l) (elim-formulas r) c
    ≡⟨ ↓-presʳ D (elim-formulas l) (elim-formulas r) c ⟩
      ⟦ ↓ D ⟨ elim-formulas l , elim-formulas r ⟩ ⟧ c
    ∎

formula-elim-compiler : LanguageCompiler PropADTL (ADTL F)
formula-elim-compiler = record
  { compile = elim-formulas
  ; config-compiler = λ _ → record { to = id ; from = id }
  ; preserves = ≗→≅[] ∘ preserves
  }

PropADT≽ADT : ADTL F ≽ PropADTL
PropADT≽ADT = expressiveness-from-compiler formula-elim-compiler
