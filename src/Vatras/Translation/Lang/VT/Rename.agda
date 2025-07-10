{-|
This module renames dimensions in variation tree expressions.

The idea of this translation is to apply a renaming function `f : D₁ → D₂` to
all elements of `D₁` in the datastructure `VT D₁` to obtain a new datastructure
`VT D₂`. To prove preservation of the semantics, we also require a left inverse
`f⁻¹ : D₂ → D₁` of `f` as a proof that `f` is injective. This precondition is
necessary because a non-injective rename would reduce the number of possible
variants.
-}
module Vatras.Translation.Lang.VT.Rename where

open import Data.Bool using (if_then_else_)
open import Data.List as List using (List; []; _∷_; _++_)
open import Data.Product using (_,_)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq using (refl; _≗_)

open import Vatras.Util.AuxProofs using (if-congˡ; if-cong)
open import Vatras.Data.EqIndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-sym)
open import Vatras.Framework.Compiler using (LanguageCompiler)
open import Vatras.Framework.Definitions using (𝔸; 𝔽)
open import Vatras.Framework.Variants as V using (Forest)
open import Vatras.Framework.Relation.Expressiveness Forest using (_≽_; expressiveness-from-compiler)
open import Vatras.Framework.Relation.Function using (from; to)
import Vatras.Data.Prop as Prop
import Vatras.Data.Prop.Rename as Prop

open import Vatras.Lang.All
open VT using (VT; UnrootedVT; VTL; _-<_>-; if[_]then[_]; if[_]then[_]else[_]; if-true[_])

open Eq.≡-Reasoning

VT-map-config : ∀ {D₁ D₂ : 𝔽}
  → (D₂ → D₁)
  → VT.Configuration D₁
  → VT.Configuration D₂
VT-map-config f config = config ∘ f

rename' : ∀ {D₁ D₂ : 𝔽} {A : 𝔸}
  → (D₁ → D₂)
  → UnrootedVT D₁ A
  → UnrootedVT D₂ A

rename'-all : ∀ {D₁ D₂ : 𝔽} {A : 𝔸}
  → (D₁ → D₂)
  → List (UnrootedVT D₁ A)
  → List (UnrootedVT D₂ A)

rename' f (a -< cs >-) = a -< rename'-all f cs >-
rename' f if[ p ]then[ l ] = if[ Prop.rename f p ]then[ rename'-all f l ]
rename' f if[ p ]then[ l ]else[ r ] = if[ Prop.rename f p ]then[ rename'-all f l ]else[ rename'-all f r ]

rename'-all f [] = []
rename'-all f (x ∷ xs) = rename' f x ∷ rename'-all f xs

rename : ∀ {D₁ D₂ : 𝔽} {A : 𝔸}
  → (D₁ → D₂)
  → VT D₁ A → VT D₂ A
rename f if-true[ l ] = if-true[ rename'-all f l ]

module _ {D₁ D₂ : 𝔽} {A : 𝔸} (f : D₁ → D₂) where
  preserves-⊆ : (expr : UnrootedVT D₁ A)
    → VT.configure (rename' f expr) ⊆[ VT-map-config f ] VT.configure expr

  preserves-⊆-all : (expr : List (UnrootedVT D₁ A))
    → VT.configure-all (rename'-all f expr) ⊆[ VT-map-config f ] VT.configure-all expr

  preserves-⊆ (a -< l >-) config =
      VT.configure (rename' f (a -< l >-)) config
    ≡⟨⟩
      a V.-< VT.configure-all (rename'-all f l) config >- ∷ []
    ≡⟨ Eq.cong (λ x → a V.-< x >- ∷ []) (preserves-⊆-all l config) ⟩
      a V.-< VT.configure-all l (config ∘ f) >- ∷ []
    ≡⟨⟩
      VT.configure (a -< l >-) (config ∘ f)
    ∎
  preserves-⊆ if[ p ]then[ l ] config =
      VT.configure (rename' f (if[ p ]then[ l ])) config
    ≡⟨⟩
      (if Prop.eval (Prop.rename f p) config then VT.configure-all (rename'-all f l) config else [])
    ≡⟨ Eq.cong (if_then _ else []) (Prop.rename-spec f p config) ⟩
      (if Prop.eval p (config ∘ f) then VT.configure-all (rename'-all f l) config else [])
    ≡⟨ if-congˡ (Prop.eval p (config ∘ f)) (preserves-⊆-all l config) ⟩
      (if Prop.eval p (config ∘ f) then VT.configure-all l (config ∘ f) else [])
    ≡⟨⟩
      VT.configure (if[ p ]then[ l ]) (config ∘ f)
    ∎
  preserves-⊆ if[ p ]then[ l ]else[ r ] config =
      VT.configure (rename' f (if[ p ]then[ l ]else[ r ])) config
    ≡⟨⟩
      (if Prop.eval (Prop.rename f p) config then VT.configure-all (rename'-all f l) config else VT.configure-all (rename'-all f r) config)
    ≡⟨ Eq.cong (if_then _ else _) (Prop.rename-spec f p config) ⟩
      (if Prop.eval p (config ∘ f) then VT.configure-all (rename'-all f l) config else VT.configure-all (rename'-all f r) config)
    ≡⟨ if-cong _ (preserves-⊆-all l config) (preserves-⊆-all r config) ⟩
      (if Prop.eval p (config ∘ f) then VT.configure-all l (config ∘ f) else VT.configure-all r (config ∘ f))
    ≡⟨⟩
      VT.configure (if[ p ]then[ l ]else[ r ]) (config ∘ f)
    ∎

  preserves-⊆-all [] config = refl
  preserves-⊆-all (x ∷ xs) config = Eq.cong₂ _++_ (preserves-⊆ x config) (preserves-⊆-all xs config)

module _ {D₁ D₂ : 𝔽} {A : 𝔸} (f : D₁ → D₂) (f⁻¹ : D₂ → D₁) (f∘f⁻¹≗id : f⁻¹ ∘ f ≗ id) where
  preserves-⊇ : (expr : UnrootedVT D₁ A)
    → VT.configure expr ⊆[ VT-map-config f⁻¹ ] VT.configure (rename' f expr)

  preserves-⊇-all : (expr : List (UnrootedVT D₁ A))
    → VT.configure-all expr ⊆[ VT-map-config f⁻¹ ] VT.configure-all (rename'-all f expr)

  preserves-⊇ (a -< l >-) config =
      VT.configure (a -< l >-) config
    ≡⟨⟩
      a V.-< VT.configure-all l config >- ∷ []
    ≡⟨ Eq.cong (λ x → a V.-< x >- ∷ []) (preserves-⊇-all l config) ⟩
      a V.-< VT.configure-all (rename'-all f l) (config ∘ f⁻¹) >- ∷ []
    ≡⟨⟩
      VT.configure (rename' f (a -< l >-)) (config ∘ f⁻¹)
    ∎
  preserves-⊇ if[ p ]then[ l ] config =
      VT.configure (if[ p ]then[ l ]) config
    ≡⟨⟩
      (if Prop.eval p config then VT.configure-all l config else [])
    ≡⟨ if-congˡ (Prop.eval p config) (preserves-⊇-all l config) ⟩
      (if Prop.eval p config then VT.configure-all (rename'-all f l) (config ∘ f⁻¹) else [])
    ≡⟨ Eq.cong (if_then _ else []) (Prop.rename-preserves f f⁻¹ f∘f⁻¹≗id p config) ⟨
      (if Prop.eval (Prop.rename f p) (config ∘ f⁻¹) then VT.configure-all (rename'-all f l) (config ∘ f⁻¹) else [])
    ≡⟨⟩
      VT.configure (rename' f (if[ p ]then[ l ])) (config ∘ f⁻¹)
    ∎
  preserves-⊇ if[ p ]then[ l ]else[ r ] config =
      VT.configure (if[ p ]then[ l ]else[ r ]) config
    ≡⟨⟩
      (if Prop.eval p config then VT.configure-all l config else VT.configure-all r config)
    ≡⟨ if-cong _ (preserves-⊇-all l config) (preserves-⊇-all r config) ⟩
      (if Prop.eval p config then VT.configure-all (rename'-all f l) (config ∘ f⁻¹) else VT.configure-all (rename'-all f r) (config ∘ f⁻¹))
    ≡⟨ Eq.cong (if_then _ else _) (Prop.rename-preserves f f⁻¹ f∘f⁻¹≗id p config) ⟨
      (if Prop.eval (Prop.rename f p) (config ∘ f⁻¹) then VT.configure-all (rename'-all f l) (config ∘ f⁻¹) else VT.configure-all (rename'-all f r) (config ∘ f⁻¹))
    ≡⟨⟩
      VT.configure (rename' f (if[ p ]then[ l ]else[ r ])) (config ∘ f⁻¹)
    ∎

  preserves-⊇-all [] config = refl
  preserves-⊇-all (x ∷ xs) config = Eq.cong₂ _++_ (preserves-⊇ x config) (preserves-⊇-all xs config)

  preserves : (e : VT D₁ A)
    → VT.⟦ rename f e ⟧ ≅[ VT-map-config f ][ VT-map-config f⁻¹ ] VT.⟦ e ⟧
  preserves if-true[ e ] = preserves-⊆-all f e , preserves-⊇-all e

VT-rename : ∀ {D₁ D₂ : 𝔽}
  → (f : D₁ → D₂)
  → (f⁻¹ : D₂ → D₁)
  → f⁻¹ ∘ f ≗ id
  → LanguageCompiler (VTL D₁) (VTL D₂)
VT-rename f f⁻¹ is-inverse .LanguageCompiler.compile = rename f
VT-rename f f⁻¹ is-inverse .LanguageCompiler.config-compiler expr .to = VT-map-config f⁻¹
VT-rename f f⁻¹ is-inverse .LanguageCompiler.config-compiler expr .from = VT-map-config f
VT-rename f f⁻¹ is-inverse .LanguageCompiler.preserves expr = ≅[]-sym (preserves f f⁻¹ is-inverse expr)

VT-rename≽VT : ∀ {D₁ D₂ : Set}
  → (f : D₁ → D₂)
  → (f⁻¹ : D₂ → D₁)
  → f⁻¹ ∘ f ≗ id
  → VTL D₂ ≽ VTL D₁
VT-rename≽VT f f⁻¹ is-inverse = expressiveness-from-compiler (VT-rename f f⁻¹ is-inverse)
