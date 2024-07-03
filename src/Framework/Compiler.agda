module Framework.Compiler where

open import Framework.Definitions
open import Framework.VariabilityLanguage
open import Framework.Relation.Function using (_⇔_; to; from; to-is-Embedding)

open import Relation.Binary.PropositionalEquality as Eq using (_≗_)
open import Data.Product using (_×_)
open import Function using (id; _∘_)

open import Data.EqIndexedSet using (_≅_; _≅[_][_]_; ≅[]-trans)

{-|
A translated configuration is extensionally equal.
Fixme: Give me a proper name not this ugly one.
-}
record LanguageCompiler {V} (Γ₁ Γ₂ : VariabilityLanguage V) : Set₁ where
  private
    L₁ = Expression Γ₁
    L₂ = Expression Γ₂
    ⟦_⟧₁ = Semantics Γ₁
    ⟦_⟧₂ = Semantics Γ₂

  field
    compile         : ∀ {A} → L₁ A → L₂ A
    config-compiler : ∀ {A} → L₁ A → Config Γ₁ ⇔ Config Γ₂
    preserves : ∀ {A} (e : L₁ A)
      → ⟦ e ⟧₁ ≅[ to (config-compiler e) ][ from (config-compiler e) ] ⟦ compile e ⟧₂
                -- TODO: It might nice to have syntax
                --   ≅[ config-compiler ]
                -- to abbreviate
                --   ≅[ to config-compiler ][ from config-compiler ].

  conf : ∀ {A} → L₁ A → Config Γ₁ → Config Γ₂
  conf e = to   (config-compiler e)

  fnoc : ∀ {A} → L₁ A → Config Γ₂ → Config Γ₁
  fnoc e = from (config-compiler e)

_⊕ᶜᶜ_ : ∀ {C₁ C₂ C₃ : ℂ}
  → C₁ ⇔ C₂
  → C₂ ⇔ C₃
  → C₁ ⇔ C₃
1→2 ⊕ᶜᶜ 2→3 = record
  { to   = to   2→3 ∘ to   1→2
  ; from = from 1→2 ∘ from 2→3
  }

⊕ᶜᶜ-stable :
  ∀ {C₁ C₂ C₃ : ℂ}
    (1→2 : C₁ ⇔ C₂) (2→3 : C₂ ⇔ C₃)
  → to-is-Embedding 1→2
  → to-is-Embedding 2→3
    --------------------
  → to-is-Embedding (1→2 ⊕ᶜᶜ 2→3)
⊕ᶜᶜ-stable 1→2 2→3 s1 s2 c₁ =
  let open Eq.≡-Reasoning in
  begin
    from 1→2 (from 2→3 (to 2→3 (to 1→2 c₁)))
  ≡⟨⟩
    from 1→2 ((from 2→3 ∘ to 2→3) (to 1→2 c₁))
  ≡⟨ Eq.cong (from 1→2) (s2 (to 1→2 c₁)) ⟩
    from 1→2 (id (to 1→2 c₁))
  ≡⟨⟩
    from 1→2 (to 1→2 c₁)
  ≡⟨ s1 c₁ ⟩
    id c₁
  ∎

_⊕_ : ∀ {V}
        {Γ₁ : VariabilityLanguage V}
        {Γ₂ : VariabilityLanguage V}
        {Γ₃ : VariabilityLanguage V}
      → LanguageCompiler Γ₁ Γ₂
      → LanguageCompiler Γ₂ Γ₃
      → LanguageCompiler Γ₁ Γ₃
_⊕_ {V} {Γ₁} {Γ₂} {Γ₃} L₁→L₂ L₂→L₃ = record
  { compile = compile L₂→L₃ ∘ compile L₁→L₂
  ; config-compiler = λ expr → record { to = conf' expr; from = fnoc' expr }
  ; preserves = p
  }
  where open LanguageCompiler
        L₁ = Expression Γ₁
        ⟦_⟧₁ = Semantics Γ₁
        ⟦_⟧₃ = Semantics Γ₃

        conf' : ∀ {A} → Expression Γ₁ A → Config Γ₁ → Config Γ₃
        conf' expr = conf L₂→L₃ (compile L₁→L₂ expr) ∘ conf L₁→L₂ expr

        fnoc' : ∀ {A} → Expression Γ₁ A → Config Γ₃ → Config Γ₁
        fnoc' expr = fnoc L₁→L₂ expr ∘ fnoc L₂→L₃ (compile L₁→L₂ expr)

        -- this pattern is very similar of ⊆[]-trans
        p : ∀ {A : 𝔸} (e : L₁ A) → ⟦ e ⟧₁ ≅[ conf' e ][ fnoc' e ] ⟦ compile L₂→L₃ (compile L₁→L₂ e) ⟧₃
        p e = ≅[]-trans (preserves L₁→L₂ e) (preserves L₂→L₃ (compile L₁→L₂ e))

-- _⊕ᶜ_ : ∀ {K} {VC₁ VC₂ VC₃ : VariabilityConstruct K}
--   → ConstructCompiler VC₁ VC₂
--   → ConstructCompiler VC₂ VC₃
--   → ConstructCompiler VC₁ VC₃
-- _⊕ᶜ_ {K} {VC₁} {_} {VC₃} 1→2 2→3 = record
--   { compile = compile 2→3 ∘ compile 1→2
--   ; config-compiler = cc
--   ; stable = stb
--   ; preserves = Pres.p
--   }
--   where open ConstructCompiler
--         open VariabilityConstruct VC₁ renaming (Construct to C₁; construct-semantics to sem₁)
--         open VariabilityConstruct VC₃ renaming (construct-semantics to sem₃)

--         cc : ConfigCompiler K K
--         cc = config-compiler 1→2 ⊕ᶜᶜ config-compiler 2→3

--         stb : Ktable cc
--         stb = ⊕ᶜᶜ-stable (config-compiler 1→2) (config-compiler 2→3) (stable 1→2) (stable 2→3)

--         module Pres {V : 𝕍} {A : 𝔸} where
--           open IVSet V A using (_≅_; ≅-trans)

--           p : ∀ {Γ : VariabilityLanguage V K}
--               → (c : C₁ (Expression Γ) A)
--               → sem₁ Γ id c ≅ sem₃ Γ (to cc) (compile 2→3 (compile 1→2 c))
--           p c = ≅-trans (preserves 1→2 c) {!preserves 2→3 (compile 1→2 c)!} --
--           -- p c₁ = ≅-trans (preserves 1→2 c₁) (preserves 2→3 (compile 1→2 c₁))
