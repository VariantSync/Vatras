{-# OPTIONS --sized-types #-}
module Framework.Constructors where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Fin using (Fin)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_×_; Σ-syntax; proj₁; proj₂) renaming (_,_ to _and_)
open import Data.List using (List; _∷_; []; map)
open import Data.List.NonEmpty using (List⁺; _∷_)

open import Function using (_∘_)
open import Level using (0ℓ)
open import Relation.Binary using (Setoid)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl; inspect; [_])
open import Relation.Nullary.Negation using (¬_)

open import Util.List using (find-or-last; find-or-last-zero) --lookup-clamped)

import Data.IndexedSet

-- some atomic data
𝔸 : Set₁
𝔸 = Set

private
  variable
    A : 𝔸

-- Variability Language
𝕃 : Set₁
𝕃 = 𝔸 → Set

-- Variant Language
𝕍 : Set₁
𝕍 = 𝔸 → Set

-- Constructor Type
ℂ : Set₁
ℂ = 𝔸 → Set

-- Annotation Language
𝔽 : Set₁
𝔽 = Set

-- Selections Language (the semantic domain of an annotation language 𝔽)
𝕊 : Set₁
𝕊 = Set

-- Configurations: A configuration is anything that allows us to do a lookup.
record Config (F : 𝔽) (S : 𝕊) : Set where
  field
    lookup : F → S
open Config public

-- Semantics of variability languages
𝕃-Semantics : 𝕍 → 𝔽 → 𝕊 → 𝕃 → 𝔸 → Set
𝕃-Semantics V F S L A = L A → Config F S → V A

-- A variability language consists of syntax and semantics (syntax is a keyword in Agda)
record VariabilityLanguage (V : 𝕍) (F : 𝔽) (S : 𝕊) : Set₁ where
  constructor _+_
  field
    expressions : 𝕃
    semantics   : 𝕃-Semantics V F S expressions A
open VariabilityLanguage public

-- Semantics of constructors
ℂ-Semantics : 𝕍 → 𝔽 → 𝕊 → (𝕃 → ℂ) → 𝔸 → Set₁
ℂ-Semantics V F S C A = (L : VariabilityLanguage V F S) → C (expressions L) A → Config F S → V A

record _∈_ (Constructor : ℂ) (Expression : 𝕃) : Set₁ where
  field
    cons : Constructor A → Expression A
    snoc : Expression  A → Maybe (Constructor A)
    id-l : snoc {A} ∘ cons {A} ≗ just
open _∈_ public

_∉_ : ℂ → 𝕃 → Set₁
C ∉ L = ¬ (C ∈ L)

_⊆_ : 𝕃 → 𝕃 → Set₁
L₁ ⊆ L₂ = ∀ (C : ℂ) → C ∈ L₁ → C ∈ L₂

_≅_ : 𝕃 → 𝕃 → Set₁
L₁ ≅ L₂ = L₁ ⊆ L₂ × L₂ ⊆ L₁

----- EXAMPLES FOR VARIANT TYPES -----

data GrulerVariant : 𝕍 where
  asset : A → GrulerVariant A
  _∥_   : GrulerVariant A → GrulerVariant A → GrulerVariant A

---- EXAMPLES FOR CONSTRUCTORS ----

record Leaf (A : 𝔸) : Set where
  constructor leaf
  field
    val : A

record Artifact (L : 𝕃) (A : 𝔸) : Set where
  constructor _-<_>-
  field
    val : A
    children : List (L A)

record ParallelComposition (L : 𝕃) (A : 𝔸) : Set where
  constructor _∥_
  field
    l : L A
    r : L A

record BinaryChoice (F : 𝔽) (L : 𝕃) (A : 𝔸) : Set where
  constructor _⟨_,_⟩
  field
    D : F
    l : L A
    r : L A

record Choice (F : 𝔽) (L : 𝕃) (A : 𝔸) : Set where
  constructor _⟨_⟩
  field
    D : F
    alternatives : List⁺ (L A)


---- SEMANTICS ----

Leaf-Semantics : ∀ {F : 𝔽} {S : 𝕊} {A : 𝔸}
  → ℂ-Semantics GrulerVariant F S (λ _ → Leaf) A
Leaf-Semantics _ (leaf a) _ = asset a

ParallelComposition-Semantics : ∀ {F : 𝔽} {S : 𝕊} {A : 𝔸}
  → ℂ-Semantics GrulerVariant F S ParallelComposition A
ParallelComposition-Semantics L (l ∥ r) c = ⟦ l ⟧ᵢ c ∥ ⟦ r ⟧ᵢ c
  where ⟦_⟧ᵢ = semantics L

BinaryChoice-Semantics : ∀ {V : 𝕍} {F : 𝔽} {A : 𝔸}
  → ℂ-Semantics V F Bool (BinaryChoice F) A
BinaryChoice-Semantics L (D ⟨ l , r ⟩) c = ⟦ if lookup c D then l else r ⟧ᵢ c
  where ⟦_⟧ᵢ = semantics L

Choice-Semantics : ∀ {V : 𝕍} {F : 𝔽} {A : 𝔸}
  → ℂ-Semantics V F ℕ (Choice F) A
Choice-Semantics L (D ⟨ alternatives ⟩) c = ⟦ find-or-last (lookup c D) alternatives ⟧ᵢ c
  where ⟦_⟧ᵢ = semantics L

---- EXAMPLE : Gruler's language -----
-- All these language implementations are super straighforward and could in fact be generated if Agda would have macros!
data Gruler : 𝕃 where
  GAsset  : Leaf A                       → Gruler A
  GPComp  : ParallelComposition Gruler A → Gruler A
  GChoice : BinaryChoice ℕ Gruler A      → Gruler A

-- I have no idea how we could prove this terminating but let's just avoid that headache.
{-# TERMINATING #-}
⟦_⟧ᵍ : 𝕃-Semantics GrulerVariant ℕ Bool Gruler A

GrulerVL : VariabilityLanguage GrulerVariant ℕ Bool
GrulerVL = record
  { expressions = Gruler
  ; semantics   = ⟦_⟧ᵍ
  }

⟦ GAsset A  ⟧ᵍ = Leaf-Semantics GrulerVL A
⟦ GPComp PC ⟧ᵍ = ParallelComposition-Semantics GrulerVL PC
⟦ GChoice C ⟧ᵍ = BinaryChoice-Semantics GrulerVL C

gruler-has-leaf : Leaf ∈ Gruler
gruler-has-leaf = record
  { cons = GAsset
  ; snoc = snoc'
  ; id-l = λ _ → refl
  }
  where snoc' : Gruler A → Maybe (Leaf A)
        snoc' (GAsset A)  = just A
        snoc' _ = nothing

gruler-has-choice : BinaryChoice ℕ Gruler ∈ Gruler
gruler-has-choice = record
  { cons = GChoice
  ; snoc = snoc'
  ; id-l = λ _ → refl
  }
  where snoc' : Gruler A → Maybe (BinaryChoice ℕ Gruler A)
        snoc' (GChoice C) = just C
        snoc' _ = nothing

----- EXAMPLE USAGES OF CONSTRUCTORS -----

make-leaf :
  ∀ (L : 𝕃) → Leaf ∈ L
  → {A : 𝔸} → A
  → L A
make-leaf _ mkLeaf a = cons mkLeaf (leaf a)

make-choice : ∀ {F : 𝔽}
  → (L : 𝕃) → BinaryChoice F L ∈ L
  → {A : 𝔸} → F → L A → L A → L A
make-choice L mkChoice D l r = cons mkChoice (D ⟨ l , r ⟩)

make-gruler-leaf : A → Gruler A
make-gruler-leaf = make-leaf Gruler gruler-has-leaf

make-gruler-choice : ℕ → Gruler A → Gruler A → Gruler A
make-gruler-choice = make-choice Gruler gruler-has-choice

----- NOW MAKE USE OF THE NEW DEFINITIONS -----

VariantSetoid : 𝕍 → 𝔸 → Setoid 0ℓ 0ℓ
VariantSetoid V A = Eq.setoid (V A)

IndexedVMap : 𝕍 → 𝔸 → Set → Set
IndexedVMap V A I = IndexedSet I
  where open Data.IndexedSet (VariantSetoid V A) using (IndexedSet)

{-|
Variant maps constitute the semantic domain of variability languages.
While we defined variant maps to be indexed sets with an arbitrary finite and non-empty index set, we directly reflect these properties
via Fin (suc n) here for convenience.
-}
VMap : 𝕍 → 𝔸 → ℕ → Set
VMap V A n = IndexedVMap V A (Fin (suc n))

Complete : ∀ {V F S} → VariabilityLanguage V F S → Set₁
Complete {V} (L + ⟦_⟧) = ∀ {A n}
  → (vs : VMap V A n)
    ----------------------------------
  → Σ[ e ∈ L A ]
      (let open Data.IndexedSet (VariantSetoid V A) renaming (_≅_ to _≋_)
        in vs ≋ ⟦ e ⟧)

record TranslationResult {V F S₁ S₂} (L₁ : VariabilityLanguage V F S₁) (L₂ : VariabilityLanguage V F S₂) : Set₁ where
  field
    expr : expressions L₂ A
    conf : Config F S₁ → Config F S₂
    fnoc : Config F S₂ → Config F S₁
open TranslationResult public

Translation : ∀ {V F S₁ S₂} (L₁ : VariabilityLanguage V F S₁) (L₂ : VariabilityLanguage V F S₂) → Set₁
Translation L₁ L₂ = ∀ {A : 𝔸} → expressions L₁ A → TranslationResult L₁ L₂

Conf-Preserves :  ∀ {V F S₁ S₂}
  → (L₁ : VariabilityLanguage V F S₁)
  → (L₂ : VariabilityLanguage V F S₂)
  → expressions L₁ A
  → expressions L₂ A
  → (Config F S₁ → Config F S₂)
  → Set
Conf-Preserves {F = F} {S₁ = S₁} L₁ L₂ e₁ e₂ conf =
  ∀ (c₁ : Config F S₁) → ⟦ e₁ ⟧₁ c₁ ≡ ⟦ e₂ ⟧₂ (conf c₁)
  where ⟦_⟧₁ = semantics L₁
        ⟦_⟧₂ = semantics L₂

Fnoc-Preserves :  ∀ {V F S₁ S₂}
  → (L₁ : VariabilityLanguage V F S₁)
  → (L₂ : VariabilityLanguage V F S₂)
  → expressions L₁ A
  → expressions L₂ A
  → (Config F S₂ → Config F S₁)
  → Set
Fnoc-Preserves {F = F} {S₂ = S₂} L₁ L₂ e₁ e₂ fnoc =
  ∀ (c₂ : Config F S₂) → ⟦ e₂ ⟧₂ c₂ ≡ ⟦ e₁ ⟧₁ (fnoc c₂)
  where ⟦_⟧₁ = semantics L₁
        ⟦_⟧₂ = semantics L₂

_⊆-via_ : ∀ {V F S₁ S₂} {L₁ : VariabilityLanguage V F S₁} {L₂ : VariabilityLanguage V F S₂}
  → (e : expressions L₁ A)
  → Translation L₁ L₂
  → Set
_⊆-via_ {L₁ = L₁} {L₂ = L₂} e₁ translate = Conf-Preserves L₁ L₂ e₁ (expr (translate e₁)) (conf (translate e₁))

_⊇-via_ : ∀ {V F S₁ S₂} {L₁ : VariabilityLanguage V F S₁} {L₂ : VariabilityLanguage V F S₂}
  → (e : expressions L₁ A)
  → Translation L₁ L₂
  → Set
_⊇-via_ {L₁ = L₁} {L₂ = L₂} e₁ translate = Fnoc-Preserves L₁ L₂ e₁ (expr (translate e₁)) (fnoc (translate e₁))

_≚-via_ : ∀ {V F S₁ S₂} {L₁ : VariabilityLanguage V F S₁} {L₂ : VariabilityLanguage V F S₂}
  → (e : expressions L₁ A)
  → Translation L₁ L₂
  → Set
e ≚-via t = e ⊆-via t × e ⊇-via t

_is-variant-preserving :  ∀ {V F S₁ S₂} {L₁ : VariabilityLanguage V F S₁} {L₂ : VariabilityLanguage V F S₂} → Translation L₁ L₂ → Set₁
_is-variant-preserving {L₁ = L₁} t = ∀ {A : 𝔸} → (e₁ : expressions L₁ A) → e₁ ≚-via t

-- any language with artifacts and choices is complete
choices-make-complete : ∀ {V F S}
  → (VL : VariabilityLanguage V F S)
  → (let L = expressions VL in
      Artifact L ∈ L
    → Choice F L ∈ L
    → Complete VL)
-- TODO: Reuse the proof that variant lists are complete. Then show that
--       every language with at least artifacts and choices is at least
--       as expressive as a variant list.
choices-make-complete VL mkArtifact mkChoice vs = {!!}

module 2→N-Choice {F : 𝔽} where
  {-|
  ConfSpec and FnocSpec define the requirements we have on translated configurations
  to prove preservation of the conversion from binary to n-ary choices.
  -}
  record ConfSpec (f : F) (conf : Config F Bool → Config F ℕ) : Set where
    field
      false→1 : ∀ (c : Config F Bool)
        → lookup c f ≡ false
        → lookup (conf c) f ≡ 1
      true→0 : ∀ (c : Config F Bool)
        → lookup c f ≡ true
        → lookup (conf c) f ≡ 0
  open ConfSpec

  record FnocSpec (f : F) (fnoc : Config F ℕ → Config F Bool) : Set where
    field
      suc→false : ∀ {n} (c : Config F ℕ)
        → lookup c f ≡ suc n
        → lookup (fnoc c) f ≡ false
      zero→true : ∀ (c : Config F ℕ)
        → lookup c f ≡ zero
        → lookup (fnoc c) f ≡ true
  open FnocSpec

  default-conf : Config F Bool → Config F ℕ
  lookup (default-conf cb) f with lookup cb f
  ... | false = 1
  ... | true  = 0

  default-fnoc : Config F ℕ → Config F Bool
  lookup (default-fnoc cn) f with lookup cn f
  ... | zero    = true
  ... | (suc _) = false

  default-conf-satisfies-spec : ∀ (f : F) → ConfSpec f default-conf
  false→1 (default-conf-satisfies-spec f) c cf≡false rewrite cf≡false = refl
  true→0  (default-conf-satisfies-spec f) c cf≡true  rewrite cf≡true  = refl

  default-fnoc-satisfies-spec : ∀ (f : F) → FnocSpec f default-fnoc
  suc→false (default-fnoc-satisfies-spec f) c cf≡suc  rewrite cf≡suc  = refl
  zero→true (default-fnoc-satisfies-spec f) c cf≡zero rewrite cf≡zero = refl

  module Translate {V}
    (VL₁ : VariabilityLanguage V F Bool)
    (VL₂ : VariabilityLanguage V F ℕ)
    (t : expressions VL₁ A → expressions VL₂ A)
    where
    private
      L₁   = expressions VL₁
      L₂   = expressions VL₂
      ⟦_⟧₁ = semantics VL₁
      ⟦_⟧₂ = semantics VL₂

    convert : BinaryChoice F L₁ A → Choice F L₂ A
    convert (D ⟨ l , r ⟩) = D ⟨ t l ∷ t r ∷ [] ⟩

    module Preservation
      (confi : Config F Bool → Config F ℕ)
      (fnoci : Config F ℕ → Config F Bool)
      (D : F)
      (l r : expressions VL₁ A)
      where
      open Data.IndexedSet (VariantSetoid V A) using (⊆-by-index-translation) renaming (_≅_ to _≋_)

      private
        2Config = Config F Bool
        NConfig = Config F ℕ

      preserves-conf :
          ConfSpec D confi
        → Conf-Preserves VL₁ VL₂ l (t l) confi
        → Conf-Preserves VL₁ VL₂ r (t r) confi
        → (c : 2Config)
        →   BinaryChoice-Semantics VL₁ (D ⟨ l , r ⟩) c
          ≡ Choice-Semantics       VL₂ (convert (D ⟨ l , r ⟩)) (confi c)
      preserves-conf conv t-l t-r c with lookup c D in eq
      ... | false rewrite false→1 conv c eq = t-r c
      ... | true  rewrite true→0  conv c eq = t-l c

      preserves-fnoc :
          FnocSpec D fnoci
        → Fnoc-Preserves VL₁ VL₂ l (t l) fnoci
        → Fnoc-Preserves VL₁ VL₂ r (t r) fnoci
        → (c : NConfig)
        →   Choice-Semantics       VL₂ (convert (D ⟨ l , r ⟩)) c
          ≡ BinaryChoice-Semantics VL₁ (D ⟨ l , r ⟩) (fnoci c)
      preserves-fnoc vnoc t-l t-r c with lookup c D in eq
      ... | zero  rewrite zero→true vnoc c eq = t-l c
      ... | suc _ rewrite suc→false vnoc c eq = t-r c

      convert-preserves :
        ∀ (conv : ConfSpec D confi)
        → (vnoc : FnocSpec D fnoci)
        -- boilerplaty induction hypothesis
        → Conf-Preserves VL₁ VL₂ l (t l) confi
        → Fnoc-Preserves VL₁ VL₂ l (t l) fnoci
        → Conf-Preserves VL₁ VL₂ r (t r) confi
        → Fnoc-Preserves VL₁ VL₂ r (t r) fnoci
        →   BinaryChoice-Semantics VL₁ (D ⟨ l , r ⟩)
          ≋ Choice-Semantics       VL₂ (convert (D ⟨ l , r ⟩))
      convert-preserves conv vnoc conf-l fnoc-l conf-r fnoc-r =
            ⊆-by-index-translation confi (preserves-conf conv conf-l conf-r)
        and ⊆-by-index-translation fnoci (preserves-fnoc vnoc fnoc-l fnoc-r)

record IndexedDimension (F : 𝔽) : Set where
  constructor _∙_
  field
    dim : F
    index : ℕ

module N→2-Choice {V F}
  (VL₁ : VariabilityLanguage V F ℕ)
  (VL₂ : VariabilityLanguage V (IndexedDimension F) Bool)
  (L₂-has-choices : BinaryChoice (IndexedDimension F) (expressions VL₂) ∈ (expressions VL₂))
  (t : expressions VL₁ A → expressions VL₂ A)
  where
  open import Data.Nat.Show using (show)

  private
    I = IndexedDimension F
    NConfig = Config F ℕ
    2Config = Config I Bool
    L₁   = expressions VL₁
    L₂   = expressions VL₂
    ⟦_⟧₁ = semantics VL₁
    ⟦_⟧₂ = semantics VL₂
    mkChoice = cons L₂-has-choices

  -- TODO Prove termination. I have no idea why Agda thinks this to be non-terminating.
  {-# TERMINATING #-}
  choice-unroll :
      F      -- initial dimension in input formula that we translate (D in the example above).
    → List⁺ (L₁ A) -- remaining alternatives of the choice to unroll. We let this shrink recursively.
    → ℕ             -- Current alternative of the given dimension we are translating. zero is left-most alternative (pointing to u in the example above).
    → BinaryChoice I L₂ A
  choice-unroll D (e ∷ [])     n = (D ∙ n) ⟨ t e , t e ⟩
  choice-unroll D (l ∷ r ∷ es) n = (D ∙ n) ⟨ t l , mkChoice (choice-unroll D (r ∷ es) (suc n)) ⟩

  convert : Choice F L₁ A → BinaryChoice I L₂ A
  convert (D ⟨ alternatives ⟩) = choice-unroll D alternatives zero

  choice-unroll-name : ∀ (D : F) (e : L₁ A) (es : List (L₁ A)) (n : ℕ)
    → Σ[ x ∈ L₂ A ] (choice-unroll D (e ∷ es) n ≡ (D ∙ n) ⟨ t e , x ⟩)
  choice-unroll-name D e [] n = t e and refl
  choice-unroll-name D e (r ∷ rs) n = mkChoice (choice-unroll D (r ∷ rs) (suc n)) and refl

  record ConfSpec (D : F) (conf : NConfig → 2Config) : Set where
    open Data.Nat using (_<_)
    field
      {-|
      A translated, binary configuration (conf c)
      has to pick the same alternative as the original configuration c.
      This alternative is nested in the binary term.
      The nesting depth is exactly equal to the alternative index:
      - the first alternative (0) is the left alternative of the root choice at level 0
      - the second alternative (1) is the left alternative of the choice (1) in the right alternative of the root choice 0
      - and so on.
      Hence the translated, binary configuration (conf c)
      has to pick the left alternative (true)
      in the choice at nesting level (lookup c D).
      -}
      select-n : ∀ (c : NConfig)
        → (i : ℕ)
        → i ≡ lookup c D
        → lookup (conf c) (D ∙ i) ≡ true

      {-|
      All alternatives before the desired alternative must be deselected so
      that we go right until we find the correct alternative to pick.
      -}
      deselect-<n : ∀ (c : NConfig)
        → (i : ℕ)
        → i < lookup c D
        → lookup (conf c) (D ∙ i) ≡ false

      {-|
      There is no third requirement because we do not care
      for the values of the translated configuration for dimensions
      deeper than (lookup c D).
      These alternatives will never be reached upon configuration.
      -}
  open ConfSpec

  record FnocSpec (fnoc : 2Config → NConfig) : Set where
    open Data.Nat using (_<_)
    field
      {-|
      The nary config must chose index i iff
      - the alternative at nesting depth i is chosen in the binary expression
      - and no other alternative at a higher nesting depth was chosen.
      -}
      correct : ∀ (c : 2Config) (D : F) (i : ℕ)
        → lookup c (D ∙ i) ≡ true
        → (∀ (j : ℕ) → j < i → lookup c (D ∙ j) ≡ false)
        → lookup (fnoc c) D ≡ i
  open FnocSpec

  module Preservation
    (D : F)
    (confi : NConfig → 2Config)
    (fnoci : 2Config → NConfig)
    where
    open import Data.List.Relation.Unary.All using (All; []; _∷_)
    open import Data.List.NonEmpty.Relation.Unary.All using (_∷_) renaming (All to All⁺)
    open Data.IndexedSet (VariantSetoid V A) using (⊆-by-index-translation) renaming (_≅_ to _≋_)
    open import Util.AuxProofs using (if-idemp)
    open Eq.≡-Reasoning

    choice-unroll-preserves : ∀
        (n : ℕ)
        (c : NConfig)
        (conv : ConfSpec D confi)
        (eq : lookup c D ≡ suc n)
        (l : expressions VL₁ A)
        (r : expressions VL₁ A)
        (es : List (expressions VL₁ A))
        (l≡tl : semantics VL₁ l c ≡ semantics VL₂ (t l) (confi c))
        (r≡tr : semantics VL₁ r c ≡ semantics VL₂ (t r) (confi c))
        (hypot-es : All (λ e → semantics VL₁ e c ≡ semantics VL₂ (t e) (confi c)) es)
      → ⟦ find-or-last n (r ∷ es) ⟧₁ c ≡ ⟦ mkChoice (choice-unroll D (r ∷ es) 1) ⟧₂ (confi c)
    choice-unroll-preserves zero c conv cD≡+1 l r es l≡tl r≡tr hypot-es =
      begin
        ⟦ find-or-last zero (r ∷ es) ⟧₁ c
      ≡⟨ Eq.cong (λ x → ⟦ x ⟧₁ c) (find-or-last-zero r es) ⟩
        ⟦ r ⟧₁ c
      ≡⟨ {!!} ⟩
        ⟦ mkChoice (choice-unroll D (r ∷ es) 1) ⟧₂ (confi c)
      ∎
    choice-unroll-preserves (suc n) c conv eq l r cD≡n+1 l≡tl r≡tr hypot-es = {!!}

    convert-preserves-l :
        ConfSpec D confi
      → (alts : List⁺ (L₁ A))
      → (c : NConfig)
      → All⁺ (λ e → ⟦ e ⟧₁ c ≡ ⟦ t e ⟧₂ (confi c)) alts
      →   Choice-Semantics       VL₁ (D ⟨ alts ⟩) c
        ≡ BinaryChoice-Semantics VL₂ (convert (D ⟨ alts ⟩)) (confi c)
    convert-preserves-l conv (e ∷ []) c (e≡tx ∷ []) =
      begin
        Choice-Semantics VL₁ (D ⟨ e ∷ [] ⟩) c
      ≡⟨⟩
        ⟦ e ⟧₁ c
      ≡⟨ e≡tx ⟩
        ⟦ t e ⟧₂ (confi c)
      ≡⟨ Eq.cong
           (λ eq → ⟦ eq ⟧₂ (confi c))
           (Eq.sym
             (if-idemp (lookup (confi c) (D ∙ 0)))) ⟩
        ⟦ if (lookup (confi c) (D ∙ 0)) then (t e) else (t e) ⟧₂ (confi c)
      ≡⟨⟩
        BinaryChoice-Semantics VL₂ (convert (D ⟨ e ∷ [] ⟩)) (confi c)
      ∎
    convert-preserves-l conv (l ∷ r ∷ es) c (l≡tl ∷ r≡tr ∷ hypot-es) with lookup c D in eq
    ... | zero  =
      begin
        ⟦ l ⟧₁ c
      ≡⟨ l≡tl ⟩
        ⟦ t l ⟧₂ (confi c)
      ≡⟨⟩
        ⟦ if true then t l else cons L₂-has-choices (choice-unroll D (r ∷ es) 1) ⟧₂ (confi c)
      ≡⟨ Eq.cong
           (λ x → ⟦ if x then t l else cons L₂-has-choices (choice-unroll D (r ∷ es) 1) ⟧₂ (confi c))
           (Eq.sym (select-n conv c 0 (Eq.sym eq))) ⟩
        ⟦ if lookup (confi c) (D ∙ 0) then t l else cons L₂-has-choices (choice-unroll D (r ∷ es) 1) ⟧₂ (confi c)
      ≡⟨⟩
        BinaryChoice-Semantics VL₂ (convert (D ⟨ l ∷ r ∷ es ⟩)) (confi c)
      ∎
    ... | suc n =
      begin
        ⟦ find-or-last n (r ∷ es) ⟧₁ c
      ≡⟨ choice-unroll-preserves n c conv eq l r es l≡tl r≡tr hypot-es ⟩
        -- ⟦ mkChoice ((D ∙ 1) ⟨ t r , proj₁ foo ⟩) ⟧₂ (confi c)
      -- ≡⟨ Eq.cong (λ x → ⟦ mkChoice x ⟧₂ (confi c)) (Eq.sym (proj₂ foo)) ⟩
        -- Choice-Semantics VL₁ (D ⟨ r ∷ es ⟩) c
        -- ?
      -- ≡⟨ convert-preserves-l conv (r ∷ es) c ⟩
        ⟦ mkChoice (choice-unroll D (r ∷ es) 1) ⟧₂ (confi c)
      ≡⟨⟩
        ⟦ if false then t l else cons L₂-has-choices (choice-unroll D (r ∷ es) 1) ⟧₂ (confi c)
      ≡⟨ Eq.cong
           (λ x → ⟦ if x then t l else cons L₂-has-choices (choice-unroll D (r ∷ es) 1) ⟧₂ (confi c))
           (Eq.sym (deselect-<n conv c 0 {!!})) ⟩
        ⟦ if lookup (confi c) (D ∙ 0) then t l else cons L₂-has-choices (choice-unroll D (r ∷ es) 1) ⟧₂ (confi c)
      ≡⟨⟩
        BinaryChoice-Semantics VL₂ (convert (D ⟨ l ∷ r ∷ es ⟩)) (confi c)
      ∎
      where foo : Σ[ x ∈ L₂ A ] (choice-unroll D (r ∷ es) 1 ≡ (D ∙ 1) ⟨ t r , x ⟩)
            foo = choice-unroll-name (D) (r) (es) 1

    convert-preserves : ∀ (alts : List⁺ (L₁ A)) →
          Choice-Semantics       VL₁ (D ⟨ alts ⟩)
        ≋ BinaryChoice-Semantics VL₂ (convert (D ⟨ alts ⟩))
    convert-preserves = {!!}

artifact-translation :
  ∀ {L₁ L₂ A}
  → (translation : L₁ A → L₂ A)
  → Artifact L₁ A
  → Artifact L₂ A
artifact-translation t (a -< es >-) = a -< map t es >-

data 2ADT : 𝕃 where
  2ADTAsset  : Leaf A                → 2ADT A
  2ADTChoice : BinaryChoice ℕ 2ADT A → 2ADT A

{-# TERMINATING #-}
⟦_⟧-2adt : 𝕃-Semantics GrulerVariant ℕ Bool 2ADT A

2ADTVL : VariabilityLanguage GrulerVariant ℕ Bool
expressions 2ADTVL = 2ADT
semantics 2ADTVL   = ⟦_⟧-2adt

⟦ 2ADTAsset A  ⟧-2adt = Leaf-Semantics 2ADTVL A
⟦ 2ADTChoice C ⟧-2adt = BinaryChoice-Semantics 2ADTVL C

data NADT : 𝕃 where
  NADTAsset  : Leaf A          → NADT A
  NADTChoice : Choice ℕ NADT A → NADT A

{-# TERMINATING #-}
⟦_⟧-nadt : 𝕃-Semantics GrulerVariant ℕ ℕ NADT A

NADTVL : VariabilityLanguage GrulerVariant ℕ ℕ
expressions NADTVL = NADT
semantics NADTVL   = ⟦_⟧-nadt

⟦ NADTAsset A  ⟧-nadt = Leaf-Semantics NADTVL A
⟦ NADTChoice C ⟧-nadt = Choice-Semantics NADTVL C

module 2ADTVL→NADTVL {A : 𝔸} where
  {-# TERMINATING #-}
  compile : 2ADT A → NADT A

  open 2→N-Choice {ℕ} using (default-conf; default-fnoc; default-conf-satisfies-spec; default-fnoc-satisfies-spec)
  open 2→N-Choice.Translate {ℕ} 2ADTVL NADTVL compile using (convert)
  conf' = default-conf
  fnoc' = default-fnoc

  compile (2ADTAsset  a) = NADTAsset a
  compile (2ADTChoice c) = NADTChoice (convert c)

  module Preservation where
    open Eq.≡-Reasoning
    open Data.IndexedSet (VariantSetoid GrulerVariant A) using (⊆-by-index-translation) renaming (_≅_ to _≋_)
    open 2→N-Choice.Translate.Preservation {ℕ} 2ADTVL NADTVL compile conf' fnoc' using (preserves-conf; preserves-fnoc)

    preserves-l : ∀ (e : 2ADT A) → Conf-Preserves 2ADTVL NADTVL e (compile e) conf'
    preserves-l (2ADTAsset _) _ = refl
    preserves-l (2ADTChoice (D ⟨ l , r ⟩)) c =
      begin
        ⟦ 2ADTChoice (D ⟨ l , r ⟩) ⟧-2adt c
      ≡⟨⟩
        BinaryChoice-Semantics 2ADTVL (D ⟨ l , r ⟩) c
      ≡⟨ preserves-conf D l r (default-conf-satisfies-spec D) (preserves-l l) (preserves-l r) c ⟩
        Choice-Semantics NADTVL (convert (D ⟨ l , r ⟩)) (conf' c)
      ≡⟨⟩
        ⟦ compile (2ADTChoice (D ⟨ l , r ⟩)) ⟧-nadt (conf' c)
      ∎

    preserves-r : ∀ (e : 2ADT A) → Fnoc-Preserves 2ADTVL NADTVL e (compile e) fnoc'
    preserves-r (2ADTAsset _) _ = refl
    preserves-r (2ADTChoice (D ⟨ l , r ⟩)) c = preserves-fnoc D l r (default-fnoc-satisfies-spec D) (preserves-r l) (preserves-r r) c

    preserves : ∀ (e : 2ADT A) → ⟦ e ⟧-2adt ≋ ⟦ compile e ⟧-nadt
    preserves e = ⊆-by-index-translation conf' (preserves-l e)
              and ⊆-by-index-translation fnoc' (preserves-r e)
