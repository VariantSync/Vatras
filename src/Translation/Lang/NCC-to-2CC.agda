{-# OPTIONS --sized-types #-}

open import Framework.Construct using (_∈ₛ_; cons)
open import Construct.Artifact as At using () renaming (Syntax to Artifact; _-<_>- to artifact-constructor)

module Translation.Lang.NCC-to-2CC (Variant : Set → Set) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

open import Data.Bool using (true; false; if_then_else_)
open import Data.Bool.Properties as Bool
import Data.EqIndexedSet as IndexedSet
open import Data.Fin as Fin using (Fin; zero; suc)
open import Data.List as List using (List)
import Data.List.Properties as List
open import Data.Nat using (zero; suc)
open import Data.Product using (_×_) renaming (_,_ to _and_)
open import Data.Vec as Vec using (Vec; []; _∷_)
import Data.Vec.Properties as Vec
open import Framework.Compiler using (LanguageCompiler; _⊕_)
open import Framework.Definitions using (𝔸; 𝔽)
open import Framework.Relation.Expressiveness Variant using (expressiveness-from-compiler; _≽_)
open import Framework.Relation.Function using (from; to)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Size using (Size; ∞)
open import Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs)

open Eq.≡-Reasoning using (step-≡; step-≡˘; _≡⟨⟩_; _∎)
open IndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-sym)

open import Lang.2CC as 2CC using (2CC; _-<_>-; _⟨_,_⟩)
module 2CC-Sem-1 D = 2CC.Sem D Variant Artifact∈ₛVariant
open 2CC-Sem-1 using (2CCL)
module 2CC-Sem-2 {D} = 2CC.Sem D Variant Artifact∈ₛVariant
open 2CC-Sem-2 using () renaming (⟦_⟧ to ⟦_⟧₂)

open import Lang.NCC as NCC using (NCC; _-<_>-; _⟨_⟩)
module NCC-Sem-1 n D = NCC.Sem n D Variant Artifact∈ₛVariant
open NCC-Sem-1 using (NCCL)
module NCC-Sem-2 {n} {D} = NCC.Sem n D Variant Artifact∈ₛVariant
open NCC-Sem-2 using () renaming (⟦_⟧ to ⟦_⟧ₙ)

open import Translation.Lang.NCC-to-NCC Variant Artifact∈ₛVariant using (NCC→NCC)
open import Translation.Lang.NCC-to-NCC Variant Artifact∈ₛVariant using (IndexedDimension) public

artifact : ∀ {A : 𝔸} → A → List (Variant A) → Variant A
artifact a cs = cons Artifact∈ₛVariant (artifact-constructor a cs)


module 2Ary where
  translate : ∀ {i : Size} {D : 𝔽} {A : 𝔸} → NCC (sucs zero) D i A → 2CC D ∞ A
  translate (a -< cs >-) = a -< List.map translate cs >-
  translate (d ⟨ l ∷ r ∷ [] ⟩) = d ⟨ translate l , translate r ⟩

  conf : ∀ {D : 𝔽} → NCC.Configuration (sucs zero) D → 2CC.Configuration D
  conf config d with config d
  ... | zero = true
  ... | suc zero = false

  fnoc : ∀ {D : 𝔽} → 2CC.Configuration D → NCC.Configuration (sucs zero) D
  fnoc config d with config d
  ... | true = zero
  ... | false = suc zero

  preserves-⊆ : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
    → (expr : NCC (sucs zero) D i A)
    → ⟦ translate expr ⟧₂ ⊆[ fnoc ] ⟦ expr ⟧ₙ
  preserves-⊆ (a -< cs >-) config =
      ⟦ translate (a -< cs >-) ⟧₂ config
    ≡⟨⟩
      ⟦ (a -< List.map translate cs >-) ⟧₂ config
    ≡⟨⟩
      artifact a (List.map (λ e → ⟦ e ⟧₂ config) (List.map translate cs))
    ≡˘⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
      artifact a (List.map (λ e → ⟦ translate e ⟧₂ config) cs)
    ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊆ e config) cs) ⟩
      artifact a (List.map (λ e → ⟦ e ⟧ₙ (fnoc config)) cs)
    ≡⟨⟩
      ⟦ a -< cs >- ⟧ₙ (fnoc config)
    ∎
  preserves-⊆ (d ⟨ l ∷ r ∷ [] ⟩) config =
      ⟦ translate (d ⟨ l ∷ r ∷ [] ⟩) ⟧₂ config
    ≡⟨⟩
      ⟦ d ⟨ translate l , translate r ⟩ ⟧₂ config
    ≡⟨⟩
      ⟦ if config d then translate l else translate r ⟧₂ config
    ≡⟨ Bool.push-function-into-if (λ e → ⟦ e ⟧₂ config) (config d) ⟩
      (if config d then ⟦ translate l ⟧₂ config else ⟦ translate r ⟧₂ config)
    ≡⟨ Eq.cong₂ (if_then_else_ (config d)) (preserves-⊆ l config) (preserves-⊆ r config) ⟩
      (if config d then ⟦ l ⟧ₙ (fnoc config) else ⟦ r ⟧ₙ (fnoc config))
    ≡⟨ lemma ⟩
      Vec.lookup (⟦ l ⟧ₙ (fnoc config) ∷ ⟦ r ⟧ₙ (fnoc config) ∷ []) (fnoc config d)
    ≡⟨ Vec.lookup-map (fnoc config d) (λ e → ⟦ e ⟧ₙ (fnoc config)) (l ∷ r ∷ []) ⟩
      ⟦ Vec.lookup (l ∷ r ∷ []) (fnoc config d) ⟧ₙ (fnoc config)
    ≡⟨⟩
      ⟦ d ⟨ l ∷ r ∷ [] ⟩ ⟧ₙ (fnoc config)
    ∎
    where
    lemma : ∀ {A : 𝔸} {a b : A} → (if config d then a else b) ≡ Vec.lookup (a ∷ b ∷ []) (fnoc config d)
    lemma with config d
    ... | true = refl
    ... | false = refl

  preserves-⊇ : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
    → (expr : NCC (sucs zero) D i A)
    → ⟦ expr ⟧ₙ ⊆[ conf ] ⟦ translate expr ⟧₂
  preserves-⊇ (a -< cs >-) config =
      ⟦ a -< cs >- ⟧ₙ config
    ≡⟨⟩
      artifact a (List.map (λ e → ⟦ e ⟧ₙ config) cs)
    ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊇ e config) cs) ⟩
      artifact a (List.map (λ e → ⟦ translate e ⟧₂ (conf config)) cs)
    ≡⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
      artifact a (List.map (λ e → ⟦ e ⟧₂ (conf config)) (List.map translate cs))
    ≡⟨⟩
      ⟦ (a -< List.map translate cs >-) ⟧₂ (conf config)
    ≡⟨⟩
      ⟦ translate (a -< cs >-) ⟧₂ (conf config)
    ∎
  preserves-⊇ (d ⟨ l ∷ r ∷ [] ⟩) config =
      ⟦ d ⟨ l ∷ r ∷ [] ⟩ ⟧ₙ config
    ≡⟨⟩
      ⟦ Vec.lookup (l ∷ r ∷ []) (config d) ⟧ₙ config
    ≡˘⟨ Vec.lookup-map (config d) (λ e → ⟦ e ⟧ₙ config) (l ∷ r ∷ []) ⟩
      Vec.lookup (⟦ l ⟧ₙ config ∷ ⟦ r ⟧ₙ config ∷ []) (config d)
    ≡⟨ lemma ⟩
      (if conf config d then ⟦ l ⟧ₙ config else ⟦ r ⟧ₙ config)
    ≡⟨ Eq.cong₂ (if_then_else_ (conf config d)) (preserves-⊇ l config) (preserves-⊇ r config) ⟩
      (if conf config d then ⟦ translate l ⟧₂ (conf config) else ⟦ translate r ⟧₂ (conf config))
    ≡˘⟨ Bool.push-function-into-if (λ e → ⟦ e ⟧₂ (conf config)) (conf config d) ⟩
      ⟦ if conf config d then translate l else translate r ⟧₂ (conf config)
    ≡⟨⟩
      ⟦ d ⟨ translate l , translate r ⟩ ⟧₂ (conf config)
    ≡⟨⟩
      ⟦ translate (d ⟨ l ∷ r ∷ [] ⟩) ⟧₂ (conf config)
    ∎
    where
    lemma : {A : 𝔸} → {a b : A} → Vec.lookup (a ∷ b ∷ []) (config d) ≡ (if conf config d then a else b)
    lemma with config d
    ... | zero = refl
    ... | suc zero = refl

  preserves : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
    → (expr : NCC (sucs zero) D i A)
    → ⟦ translate expr ⟧₂ ≅[ fnoc ][ conf ] ⟦ expr ⟧ₙ
  preserves expr = preserves-⊆ expr and preserves-⊇ expr

  NCC→2CC : ∀ {i : Size} {D : 𝔽} → LanguageCompiler (NCCL (sucs zero) D {i}) (2CCL D)
  NCC→2CC .LanguageCompiler.compile = translate
  NCC→2CC .LanguageCompiler.config-compiler expr .to = conf
  NCC→2CC .LanguageCompiler.config-compiler expr .from = fnoc
  NCC→2CC .LanguageCompiler.preserves expr = ≅[]-sym (preserves expr)


NCC→2CC : ∀ {i : Size} {D : 𝔽} → (n : ℕ≥ 2) → LanguageCompiler (NCCL n D {i}) (2CCL (D × Fin (ℕ≥.toℕ (ℕ≥.pred n))))
NCC→2CC n = NCC→NCC n (sucs zero) ⊕ 2Ary.NCC→2CC

2CC≽NCC : ∀ {D : 𝔽} → (n : ℕ≥ 2) → 2CCL (IndexedDimension D n) ≽ NCCL n D
2CC≽NCC n = expressiveness-from-compiler (NCC→2CC n)
