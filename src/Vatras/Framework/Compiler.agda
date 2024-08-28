{-|
This module defines compilers of variability languages
and useful operators.
-}
module Vatras.Framework.Compiler where

open import Vatras.Framework.Definitions
open import Vatras.Framework.VariabilityLanguage
open import Vatras.Framework.Relation.Function using (_⇔_; to; from; to-is-Embedding)

open import Relation.Binary.PropositionalEquality as Eq using (_≗_)
open import Data.Product using (_×_)
open import Function using (id; _∘_)

open import Vatras.Data.EqIndexedSet using (_≅_; _≅[_][_]_; ≅[]-trans)

{-|
A compiler from a variability language L to another language M translates
expressions and configurations in both directions for a certain expression, and also
proves that the translation of expression preserves semantics.
-}
record LanguageCompiler {V} (L M : VariabilityLanguage V) : Set₁ where
  private
    ⟦_⟧₁ = Semantics L
    ⟦_⟧₂ = Semantics M

  field
    compile         : ∀ {A} → Expression L A → Expression M A
    config-compiler : ∀ {A} → Expression L A → Config L ⇔ Config M
    preserves : ∀ {A} (e : Expression L A)
      → ⟦ e ⟧₁ ≅[ to (config-compiler e) ][ from (config-compiler e) ] ⟦ compile e ⟧₂
                -- TODO: It might nice to have syntax
                --   ≅[ config-compiler ]
                -- to abbreviate
                --   ≅[ to config-compiler ][ from config-compiler ].

  conf : ∀ {A} → Expression L A → Config L → Config M
  conf e = to   (config-compiler e)

  fnoc : ∀ {A} → Expression L A → Config M → Config L
  fnoc e = from (config-compiler e)

{-|
Composition of configuration compilers.
This is a proof that compiling configurations
is transitive.
-}
_⊕ᶜᶜ_ : ∀ {C₁ C₂ C₃ : ℂ}
  → C₁ ⇔ C₂
  → C₂ ⇔ C₃
  → C₁ ⇔ C₃
1→2 ⊕ᶜᶜ 2→3 = record
  { to   = to   2→3 ∘ to   1→2
  ; from = from 1→2 ∘ from 2→3
  }

{-|
Proof that configuration compiler composition
preserves the compiler constituting an embedding.
-}
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

{-|
Composition of compilers for variability language.
This is a proof that compiling variability languages
is transitive.
-}
_⊕_ : ∀ {V} {L M N : VariabilityLanguage V}
  → LanguageCompiler L M
  → LanguageCompiler M N
  → LanguageCompiler L N
_⊕_ {V} {L} {M} {N} L→M M→N = record
  { compile         = compile M→N ∘ compile L→M
  ; config-compiler = λ expr → record { to = conf' expr; from = fnoc' expr }
  ; preserves       = p
  }
  where
    open LanguageCompiler
    ⟦_⟧₁ = Semantics L
    ⟦_⟧₃ = Semantics N

    conf' : ∀ {A} → Expression L A → Config L → Config N
    conf' expr = conf M→N (compile L→M expr) ∘ conf L→M expr

    fnoc' : ∀ {A} → Expression L A → Config N → Config L
    fnoc' expr = fnoc L→M expr ∘ fnoc M→N (compile L→M expr)

    -- this pattern is very similar of ⊆[]-trans
    p : ∀ {A : 𝔸} (e : Expression L A) → ⟦ e ⟧₁ ≅[ conf' e ][ fnoc' e ] ⟦ compile M→N (compile L→M e) ⟧₃
    p e = ≅[]-trans (preserves L→M e) (preserves M→N (compile L→M e))
