module Framework.V2.Compiler where

open import Framework.V2.Definitions
open import Relation.Binary.PropositionalEquality as Eq using (_≗_)
open import Data.Product using (_×_)
open import Function using (id; _∘_)
import Data.IndexedSet

module IVSet (V : 𝕍) (A : 𝔸) = Data.IndexedSet (Eq.setoid (V A))

ConfigTranslation : ∀ (F₁ : 𝔽) (S₁ : 𝕊) (F₂ : 𝔽) (S₂ : 𝕊) → Set
ConfigTranslation F₁ S₁ F₂ S₂ = Config F₁ S₁ → Config F₂ S₂

record ConfigCompiler (F₁ : 𝔽) (S₁ : 𝕊) (F₂ : 𝔽) (S₂ : 𝕊) : Set where
  field
    to   : ConfigTranslation F₁ S₁ F₂ S₂
    from : ConfigTranslation F₂ S₂ F₁ S₁
open ConfigCompiler public

{-|
A translated configuration is extensionally equal.
Fixme: Give me a proper name not this ugly one.
-}
ExtensionallyEqual-Translation : ∀ {F S} → ConfigTranslation F S F S → Set
ExtensionallyEqual-Translation f = ∀ c → f c ≗ c

ExtensionallyEqual : ∀ {F S} → ConfigCompiler F S F S → Set
ExtensionallyEqual record { to = to ; from = from } =
  ExtensionallyEqual-Translation to × ExtensionallyEqual-Translation from

-- We identify a configuration to be the same if it can be uniquely translated back
-- (i.e., if `to` is an embedding into the second configuration language via its inverse `from`).
-- We do not require the inverse direction `from`, being an embedding of configurations from `C₂` into `C₁`, because `C₂` could be larger than `C₁` (when interpreted as a set).
-- For example, the set of features in `C₂` could be bigger (e.g., when going from core choice calculus to binary choice calculus) but all information can be derived by `conf` from our initial configuration `c₁`.
Stable : ∀ {F₁ S₁ F₂ S₂} → ConfigCompiler F₁ S₁ F₂ S₂ → Set
Stable cc = from cc ∘ to cc ≗ id

record LanguageCompiler {V F₁ F₂ S₁ S₂} (Γ₁ : VariabilityLanguage V F₁ S₁) (Γ₂ : VariabilityLanguage V F₂ S₂) : Set₁ where
  private
    L₁ = Expression Γ₁
    L₂ = Expression Γ₂
    ⟦_⟧₁ = Semantics Γ₁
    ⟦_⟧₂ = Semantics Γ₂

  field
    compile         : ∀ {A} → L₁ A → L₂ A
    config-compiler : ConfigCompiler F₁ S₁ F₂ S₂
    preserves : ∀ {A} → let open IVSet V A using (_≅[_][_]_) in
                ∀ (e : L₁ A) → ⟦ e ⟧₁ ≅[ to config-compiler ][ from config-compiler ] ⟦ compile e ⟧₂
                -- TODO: It might nice to have syntax
                --   ≅[ config-compiler ]
                -- to abbreviate
                --   ≅[ to config-compiler ][ from config-compiler ].

  conf = to   config-compiler
  fnoc = from config-compiler

-- Compiles a single construct to another one without altering the underlying sub expressions.
-- FIXME: This definition might be too abstract.
--        To preserve semantics, most of the time, additional requirements on the
--        config translations are required which are currently not part of the
--        preservation theorem here. Maybe we have to add these constraints as type parameters here?
record ConstructCompiler {F S} (VC₁ VC₂ : VariabilityConstruct F S) : Set₁ where
  open VariabilityConstruct VC₁ renaming (Construct to C₁; construct-semantics to sem₁)
  open VariabilityConstruct VC₂ renaming (Construct to C₂; construct-semantics to sem₂)

  field
    -- TODO: F and S might change. Example: Binary to Nary choices.
    compile : ∀ {E A} → C₁ F E A → C₂ F E A
    preserves : ∀ {V} {Γ : VariabilityLanguage V F S} {A}
      → (c₁ : C₁ F (Expression Γ) A)
      → let open IVSet V A using (_≅_) in
        sem₁ Γ id c₁ ≅ sem₂ Γ id (compile c₁) -- maybe add conf and fnoc here?

{-|
Compiles languages below construcst.
This means that an expression in a language Γ₁ of which we know that it has a specific
syntactic construct VC at the top is compiled to Γ₂ retaining the very same construct at the top.
-}
record ConstructFunctor {F S} (VC : VariabilityConstruct F S) : Set₁ where
  open VariabilityConstruct VC
  open LanguageCompiler using (conf; fnoc; compile; config-compiler)

  field
    map : ∀ {A} {L₁ L₂ : 𝔼}
      → (L₁ A → L₂ A)
      → Construct F L₁ A
      → Construct F L₂ A
    preserves : ∀ {V} {F'} {S'} {Γ₁ : VariabilityLanguage V F S} {Γ₂ : VariabilityLanguage V F' S'} {A}
      → let open IVSet V A using (_≅[_][_]_) in
      ∀ (t : LanguageCompiler Γ₁ Γ₂)
      → (c : Construct F (Expression Γ₁) A)
      → Stable (config-compiler t)
      → construct-semantics Γ₁ id c
          ≅[ conf t ][ fnoc t ]
        construct-semantics Γ₂ (fnoc t) (map (compile t) c)

_⊕ˡ_ : ∀ {V} {F₁ F₂ F₃} {S₁ S₂ S₃}
        {Γ₁ : VariabilityLanguage V F₁ S₁}
        {Γ₂ : VariabilityLanguage V F₂ S₂}
        {Γ₃ : VariabilityLanguage V F₃ S₃}
      → LanguageCompiler Γ₁ Γ₂
      → LanguageCompiler Γ₂ Γ₃
      → LanguageCompiler Γ₁ Γ₃
_⊕ˡ_ {V} {F₁} {F₂} {F₃} {S₁} {S₂} {S₃} {Γ₁} {Γ₂} {Γ₃} L₁→L₂ L₂→L₃ = record
  { compile = compile L₂→L₃ ∘ compile L₁→L₂
  ; config-compiler = record { to = conf'; from = fnoc' }
  ; preserves = p
  }
  where open LanguageCompiler
        L₁ = Expression Γ₁
        ⟦_⟧₁ = Semantics Γ₁
        ⟦_⟧₃ = Semantics Γ₃

        conf' : Config F₁ S₁ → Config F₃ S₃
        conf' = conf L₂→L₃ ∘ conf L₁→L₂

        fnoc' : Config F₃ S₃ → Config F₁ S₁
        fnoc' = fnoc L₁→L₂ ∘ fnoc L₂→L₃

        module _ {A : 𝔸} where
          open IVSet V A using (_≅[_][_]_; ≅[]-trans)

          -- this pattern is very similar of ⊆[]-trans
          p : ∀ (e : L₁ A) → ⟦ e ⟧₁ ≅[ conf' ][ fnoc' ] ⟦ compile L₂→L₃ (compile L₁→L₂ e) ⟧₃
          p e = ≅[]-trans (preserves L₁→L₂ e) (preserves L₂→L₃ (compile L₁→L₂ e))

-- _⊕ᶜ_ : ∀ {V F S} {VC₁ VC₂ VC₃ : VariabilityConstruct V F S}
--   → ConstructCompiler VC₁ VC₂
--   → ConstructCompiler VC₂ VC₃
--   → ConstructCompiler VC₁ VC₃
-- _⊕ᶜ_ {V} {F} {S} {VC₁} {_} {VC₃} 1→2 2→3 = record
--   { compile = compile 2→3 ∘ compile 1→2
--   ; preserves = Pres.p
--   }
--   where open ConstructCompiler
--         open VariabilityConstruct VC₁ renaming (Construct to C₁; _⊢⟦_⟧ to _⊢⟦_⟧₁)
--         open VariabilityConstruct VC₃ renaming (_⊢⟦_⟧ to _⊢⟦_⟧₃)

--         module Pres {A : 𝔸} where
--           open IVSet V A using (_≅_; ≅-trans)

--           p : ∀ {Γ : VariabilityLanguage V F S}
--               → (c₁ : C₁ F (Expression Γ) A)
--               → Γ ⊢⟦ c₁ ⟧₁ ≅ Γ ⊢⟦ compile 2→3 (compile 1→2 c₁) ⟧₃
--           p c₁ = ≅-trans (preserves 1→2 c₁) (preserves 2→3 (compile 1→2 c₁))
