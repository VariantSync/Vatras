# Syntactic Comparisons

## Options

```agda
{-# OPTIONS --sized-types #-}
```

## Module

```agda
module Relations.Syntactic where
```

## Imports

```agda
open import Data.List using ([]; _∷_; map)
open import Data.Product using (∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (id; _∘_)

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; _≗_; refl)
open Eq.≡-Reasoning

open import Definitions using (Domain; Variant; Artifactᵥ)
```

## Embedding into generic tree structure

```agda
DomainNode : Set1
DomainNode = Set -- e.g. LambdaNode

-- Variant is Skeleton
-- Domain is Animal
-- DomainNode is Flesh
record ObjectLanguage (Fail : Set) (A : Domain) (N : DomainNode) : Set where
  field
    disassemble : A → Variant N
    assemble : Variant N → A ⊎ Fail -- parse unstructured variant to structured domain data

    bi-l  : ∀ (a : A) → (assemble (disassemble a)) ≡ inj₁ a
    bi-r  : ∀ {a : A} {v : Variant N} → assemble v ≡ inj₁ a → disassemble a ≡ v

    -- Do we also have to require that Variant is a functor such that the following holds?
    -- iso-l : ∀ {f : A → A} → disassemble ∘ f ≗ (fmap f) ∘ disassemble
open ObjectLanguage public

_is-syntactically-correct-in_ : ∀ {F A N} → (v : Variant N) → (o : ObjectLanguage F A N) → Set
v is-syntactically-correct-in o = ∃[ a ] (assemble o v ≡ inj₁ a)

_is-syntax-preserving-in_ : ∀ {F A N} → (f : Variant N → Variant N) → (o : ObjectLanguage F A N) → Set
_is-syntax-preserving-in_ {N = N} f o = ∀ (v : Variant N) → v is-syntactically-correct-in o → (f v) is-syntactically-correct-in o
```

## Instances (TODO: Move to separate files)

### Lambda Calculus as a Domain
```agda
data Lambda (S : Set) : Set where
  Var : S → Lambda S
  App : Lambda S → Lambda S → Lambda S
  Fun : S → Lambda S → Lambda S

-- Flesh
data LambdaNode (S : Set) : Set where
  VarNode : S → LambdaNode S
  AppNode : LambdaNode S
  FunNode : S → LambdaNode S

open import Data.String using (String; _++_)

lambda-disassemble : ∀ {S : Set} → Lambda S → Variant (LambdaNode S)
lambda-disassemble (Var s)   = Artifactᵥ (VarNode s) []
lambda-disassemble (App l r) = Artifactᵥ AppNode (lambda-disassemble l ∷ lambda-disassemble r ∷ [])
lambda-disassemble (Fun p b) = Artifactᵥ (FunNode p) (lambda-disassemble b ∷ [])

lambda-assemble : ∀ {S : Set} → Variant (LambdaNode S) → Lambda S ⊎ String
lambda-assemble (Artifactᵥ (VarNode s) [])       = inj₁ (Var s)
lambda-assemble (Artifactᵥ (VarNode s) (e ∷ es)) = inj₂ "VarNode cannot have children!"
lambda-assemble (Artifactᵥ AppNode (vl ∷ vr ∷ [])) with lambda-assemble vl | lambda-assemble vr
... | inj₁ l      | inj₁ r      = inj₁ (App l r)
... | inj₁ l      | inj₂ r-fail = inj₂ r-fail
... | inj₂ l-fail | inj₁ r      = inj₂ l-fail
... | inj₂ l-fail | inj₂ r-fail = inj₂ (l-fail ++ "; " ++ r-fail)
lambda-assemble (Artifactᵥ AppNode _)     = inj₂ "AppNode must have exactly two children!"
lambda-assemble (Artifactᵥ (FunNode p) (b ∷ [])) with lambda-assemble b
... | inj₁ body = inj₁ (Fun p body)
... | inj₂ fail = inj₂ fail
lambda-assemble (Artifactᵥ (FunNode p) _) = inj₂ "FunNode must have exactly one child!"

lambda-bi-l : ∀ {S} (t : Lambda S) → lambda-assemble (lambda-disassemble t) ≡ inj₁ t
lambda-bi-l (Var x)   = refl
lambda-bi-l (App l r) rewrite lambda-bi-l l | lambda-bi-l r = refl
lambda-bi-l (Fun p b) rewrite lambda-bi-l b = refl

foo : ∀ {A B : Set} {a b : A} → inj₁ {B = B} a ≡ inj₁ {B = B} b → a ≡ b
foo refl = refl

bar : ∀ {A : Set} {a b : A} → Var a ≡ Var b → a ≡ b
bar refl = refl

-- somehow this proof is really weird and complicated. There must be something overlooked by me.
lambda-bi-r : ∀ {S} {t : Lambda S} {v : Variant (LambdaNode S)} →
              lambda-assemble v ≡ inj₁ t → lambda-disassemble t ≡ v

lambda-bi-r {S} {Var x} {Artifactᵥ (VarNode y) []} eq rewrite eq =
  Eq.cong (λ e → Artifactᵥ (VarNode e) []) (Eq.sym (bar (foo eq)))
lambda-bi-r {_} {Var x} {Artifactᵥ AppNode (e ∷ es)} = {!!}
lambda-bi-r {_} {Var x} {Artifactᵥ (FunNode x₁) (e ∷ es)} eq = {!!}

lambda-bi-r {_} {App l r} {Artifactᵥ (VarNode x) es} eq = {!!}
lambda-bi-r {_} {App l r} {Artifactᵥ AppNode es} eq rewrite eq = {!!}
lambda-bi-r {_} {App l r} {Artifactᵥ (FunNode x) es} eq = {!!}

lambda-bi-r {_} {Fun p b} {v} eq = {!!}

Lambda-is-OL : ∀ {S : Set} → ObjectLanguage String (Lambda S) (LambdaNode S)
Lambda-is-OL {S} = record
  { disassemble = lambda-disassemble
  ; assemble = lambda-assemble
  ; bi-l = lambda-bi-l
  ; bi-r = lambda-bi-r
  }
```

### Choice Calculus as a Domain
```agda
open import Lang.BCC
open import Lang.Annotation.Name

open import Size

data BCCNode (A : Domain) : Set where
  ArtifactNode : A         → BCCNode A
  ChoiceNode   : Dimension → BCCNode A

bcc-disassemble : ∀ {i : Size} {A : Domain} → BCC i A → Variant (BCCNode A)
bcc-disassemble (Artifact a es) = Artifactᵥ (ArtifactNode a) (map bcc-disassemble es)
bcc-disassemble (D ⟨ l , r ⟩)    = Artifactᵥ (ChoiceNode D) (bcc-disassemble l ∷ bcc-disassemble r ∷ [])

-- We need sized variants there to prove termination. :(((
bcc-assemble : ∀ {A : Domain} → Variant (BCCNode A) → BCC ∞ A ⊎ String
bcc-assemble (Artifactᵥ (ArtifactNode a) es) with map bcc-assemble es --mapM
... | x = {!!} --TODO: fold such that errors are concatenated or success is returned in case no error happened
bcc-assemble (Artifactᵥ (ChoiceNode D) (vl ∷ vr ∷ [])) with (bcc-assemble vl) | (bcc-assemble vr)
... | inj₁ l      | inj₁ r      = inj₁ (D ⟨ l , r ⟩)
... | inj₁ l      | inj₂ r-fail = inj₂ r-fail
... | inj₂ l-fail | inj₁ r      = inj₂ l-fail
... | inj₂ l-fail | inj₂ r-fail = inj₂ (l-fail ++ "; " ++ r-fail)
bcc-assemble (Artifactᵥ (ChoiceNode D) _) = inj₂ "Choice must have exactly two children!"

BCC-is-OL : ∀ {A : Domain} → ObjectLanguage String (BCC ∞ A) (BCCNode A)
BCC-is-OL = record
  { disassemble = bcc-disassemble
  ; assemble = bcc-assemble
  ; bi-l = {!!}
  ; bi-r = {!!}
  }
```
