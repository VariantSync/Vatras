open import Framework.Definitions using (𝔽; 𝕍; 𝔸; 𝔼)
open import Relation.Binary using (DecidableEquality; Rel)
module Translation.Lang.2ADT.DeadElim
  (F : 𝔽)
  (V : 𝕍)
  (_==_ : DecidableEquality F)
  where

open import Function using (id; _∘_)

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)

open import Relation.Nullary.Negation using (¬_)
open import Relation.Nullary.Decidable using (yes; no; toWitness)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl; sym)
open Eq.≡-Reasoning

open import Framework.VariabilityLanguage
open import Framework.Compiler
open import Data.EqIndexedSet using (_≅[_][_]_; ≐→≅[])
open import Lang.2ADT
open import Lang.2ADT.Path F V _==_

{-
A 2ADT is undead if it does not contain any dead branches.
This is the case if any path from the root to a leaf does not contain
a feature name twice.
-}
Undead : ∀ {A} (e : 2ADT V F A) → Set
Undead e = ∀ (p : Path) → p starts-at e → Unique p

{-
A leaf node is always undead.
-}
undead-leaf : ∀ {A} {v : V A}
    ---------------
  → Undead (leaf v)
undead-leaf .[] tleaf = []

{-
If a choice is undead, so is its left alternative.
-}
undead-left : ∀ {A} {D} {l r : 2ADT V F A}
  → Undead (D ⟨ l , r ⟩)
    --------------------
  → Undead l
undead-left {D = D} u-chc p t with u-chc (D ↣ true ∷ p) (walk-left t)
... | _ ∷ u-p = u-p

{-
If a choice is undead, so is its right alternative.
-}
undead-right : ∀ {A} {D} {l r : 2ADT V F A}
  → Undead (D ⟨ l , r ⟩)
    --------------------
  → Undead r
undead-right {D = D} u-chc p t with u-chc (D ↣ false ∷ p) (walk-right t)
... | _ ∷ u-p = u-p

{-
If two expressions l and r are undead and do
not contain the feature name D,
then the choice D ⟨ l , r ⟩ is undead, too.
-}
undead-choice : ∀ {A} {D} {l r : 2ADT V F A}
  → Undead l
  → Undead r
    -- It might be handy to introduce a new predicate for containment of feature names in expressions D ∈ l later.
  → D ∉' l
  → D ∉' r
    --------------------------------------
  → Undead (D ⟨ l , r ⟩)
undead-choice u-l u-r D∉l D∉r (.(_ ↣ true ) ∷ p) (walk-left  t) = ∉→All-different p (D∉l p t) ∷ (u-l p t)
undead-choice u-l u-r D∉l D∉r (.(_ ↣ false) ∷ p) (walk-right t) = ∉→All-different p (D∉r p t) ∷ (u-r p t)

record Undead2ADT (A : 𝔸) : Set where
  constructor _⊚_ -- \oo
  field
    node   : 2ADT V F A
    undead : Undead node
open Undead2ADT public

⟦_⟧ᵤ : 𝔼-Semantics V (Configuration F) Undead2ADT
⟦_⟧ᵤ = ⟦_⟧ ∘ node

Undead2ADTL : VariabilityLanguage V
Undead2ADTL = ⟪ Undead2ADT , Configuration F , ⟦_⟧ᵤ ⟫

{-
Kills all dead branches within a given expression,
assuming that some features were already defined.
-}
kill-dead-below : ∀ {A}
  → (defined : Path)
  → 2ADT V F A
  → 2ADT V F A
kill-dead-below _ (leaf v) = leaf v
kill-dead-below defined (D ⟨ l , r ⟩) with D ∈? defined
--- The current choice was already encountered above this choice.
--- This means, this choice is dominated (see choice domination).
--- This in turn means, that one of the choice's alternatives is dead because it cannot
--- be selected anymore.
... | yes D∈defined =
  if getValue D∈defined
  then kill-dead-below defined l
  else kill-dead-below defined r
-- The current choice was not encountered before. We follow both paths recursively,
-- adding our choice information to each path.
... | no D∉defined = D ⟨ kill-dead-below (D ↣ true ∷ defined) l , kill-dead-below (D ↣ false ∷ defined) r ⟩

{-
If a feature name was already defined,
then any path starting at an expression,
in which dead branches were eliminated accordingly,
does not contain that feature name.
-}
kill-dead-eliminates-defined-features : ∀ {A}
  → (defined : Path)
  → (D : F)
  → D ∈ defined
  → (e : 2ADT V F A)
  → D ∉' kill-dead-below defined e
kill-dead-eliminates-defined-features _ _ _ (leaf _) .[] tleaf ()
kill-dead-eliminates-defined-features defined _ _ (D' ⟨ _ , _ ⟩) _ _ _ with D' ∈? defined
kill-dead-eliminates-defined-features defined D D-def (D' ⟨ l , r ⟩) p t D∈p | yes D'-def with getValue D'-def
... | true  = kill-dead-eliminates-defined-features defined D D-def l p t D∈p
... | false = kill-dead-eliminates-defined-features defined D D-def r p t D∈p
kill-dead-eliminates-defined-features _ D _ (D' ⟨ _ , _ ⟩) _ _ _
  | no ¬D'-def with D == D'
kill-dead-eliminates-defined-features _ _ D-def (_  ⟨ _ , _ ⟩) _ _ _
  | no ¬D'-def | yes refl = ⊥-elim (¬D'-def D-def)
kill-dead-eliminates-defined-features _ _       _     (D' ⟨ _ , _ ⟩) ((.D' ↣ true) ∷ _) (walk-left _) (here D=D')
  | no _       | no D≠D'  = ⊥-elim (D≠D' (toWitness D=D'))
kill-dead-eliminates-defined-features defined D D-def (D' ⟨ l , _ ⟩) ((.D' ↣ true) ∷ p) (walk-left t) (there D∈p)
  | no ¬D'-def | no D≠D'  = kill-dead-eliminates-defined-features (D' ↣ true ∷ defined) D (there D-def) l p t D∈p
kill-dead-eliminates-defined-features _ _       _     (D' ⟨ _ , _ ⟩) ((.D' ↣ false) ∷ _) (walk-right _) (here D=D')
  | no _       | no D≠D'  = ⊥-elim (D≠D' (toWitness D=D'))
kill-dead-eliminates-defined-features defined D D-def (D' ⟨ _ , r ⟩) ((.D' ↣ false) ∷ p) (walk-right t) (there D∈p)
  | no ¬D'-def | no D≠D'  = kill-dead-eliminates-defined-features (D' ↣ false ∷ defined) D (there D-def) r p t D∈p

{-
Proof that kill-dead is correct,
which means that the resulting tree
is undead.
-}
kill-dead-correct : ∀ {A}
  → (defined : Path)
  → (e : 2ADT V F A)
  → Undead (kill-dead-below defined e)
kill-dead-correct _ (leaf v) = undead-leaf
kill-dead-correct defined (D ⟨ _ , _ ⟩) with D ∈? defined
kill-dead-correct defined (_ ⟨ l , r ⟩) | yes D∈defined with getValue D∈defined
... | true  = kill-dead-correct defined l
... | false = kill-dead-correct defined r
kill-dead-correct defined (D ⟨ l , r ⟩) | no  D∉defined =
  undead-choice
  (kill-dead-correct (D ↣ true  ∷ defined) l)
  (kill-dead-correct (D ↣ false ∷ defined) r)
  (kill-dead-eliminates-defined-features (D ↣ true  ∷ defined) D (here (is-refl D true )) l)
  (kill-dead-eliminates-defined-features (D ↣ false ∷ defined) D (here (is-refl D false)) r)

{-
Dead branch elimination of 2ADTs.
-}
kill-dead : ∀ {A}
  → 2ADT V F A
  → Undead2ADT A
kill-dead e = kill-dead-below [] e ⊚ kill-dead-correct [] e

kill-dead-preserves-below-partial-configs : ∀ {A : 𝔸}
  → (e : 2ADT V F A)
  → (defined : Path)
  → (c : Configuration F)
  → defined ⊑ c
  → ⟦ e ⟧ c ≡ ⟦ kill-dead-below defined e ⟧ c
kill-dead-preserves-below-partial-configs (leaf _) _ _ _ = refl
kill-dead-preserves-below-partial-configs (D ⟨ l , r ⟩) def c def⊑c with D ∈? def
kill-dead-preserves-below-partial-configs (D ⟨ l , r ⟩) def c def⊑c | yes D∈def
  rewrite lookup-partial def⊑c D∈def
  with c D
... | true  = kill-dead-preserves-below-partial-configs l def c def⊑c
... | false = kill-dead-preserves-below-partial-configs r def c def⊑c
kill-dead-preserves-below-partial-configs (D ⟨ l , r ⟩) def c def⊑c | no D∉def
  with c D in eq
... | true  = kill-dead-preserves-below-partial-configs l ((D ↣  true) ∷ def) c (eq ∷ def⊑c)
... | false = kill-dead-preserves-below-partial-configs r ((D ↣ false) ∷ def) c (eq ∷ def⊑c)

kill-dead-preserves : ∀ {A : 𝔸}
  → (e : 2ADT V F A)
  → ⟦ e ⟧ ≅[ id ][ id ] ⟦ kill-dead e ⟧ᵤ
kill-dead-preserves e = ≐→≅[] (λ c → kill-dead-preserves-below-partial-configs e [] c [])

kill-dead-compiler : LanguageCompiler (2ADTL V F) Undead2ADTL
kill-dead-compiler = record
  { compile = kill-dead
  ; config-compiler = λ _ → record { to = id ; from = id }
  ; preserves = kill-dead-preserves
  }
