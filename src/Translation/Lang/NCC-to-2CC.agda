open import Framework.Construct using (_∈ₛ_; cons)
open import Framework.Definitions using (𝔸; 𝔽; 𝕍; atoms)
open import Construct.Artifact as At using () renaming (Syntax to Artifact; _-<_>- to artifact-constructor)

module Translation.Lang.NCC-to-2CC (Variant : 𝕍) (Artifact∈ₛVariant : Artifact ∈ₛ Variant) where

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
open import Framework.Relation.Expressiveness Variant using (expressiveness-from-compiler; _≽_)
open import Framework.Relation.Function using (from; to)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)
open import Size using (Size; ∞)
open import Util.Nat.AtLeast as ℕ≥ using (ℕ≥; sucs)

open Eq.≡-Reasoning using (step-≡-⟨; step-≡-⟩; step-≡-∣; _∎)
open IndexedSet using (_≅[_][_]_; _⊆[_]_; ≅[]-sym)

open import Lang.All.Generic Variant Artifact∈ₛVariant
open 2CC using (2CC; 2CCL; _-<_>-; _⟨_,_⟩)
open NCC using (NCC; NCCL; _-<_>-; _⟨_⟩)

open import Framework.Annotation.IndexedDimension
open import Translation.Lang.NCC.NCC-to-NCC Variant Artifact∈ₛVariant using (NCC→NCC)
artifact : ∀ {A : 𝔸} → atoms A → List (Variant A) → Variant A
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
    → 2CC.⟦ translate expr ⟧ ⊆[ fnoc ] NCC.⟦ expr ⟧
  preserves-⊆ (a -< cs >-) config =
      2CC.⟦ translate (a -< cs >-) ⟧ config
    ≡⟨⟩
      2CC.⟦ (a -< List.map translate cs >-) ⟧ config
    ≡⟨⟩
      artifact a (List.map (λ e → 2CC.⟦ e ⟧ config) (List.map translate cs))
    ≡⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟨
      artifact a (List.map (λ e → 2CC.⟦ translate e ⟧ config) cs)
    ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊆ e config) cs) ⟩
      artifact a (List.map (λ e → NCC.⟦ e ⟧ (fnoc config)) cs)
    ≡⟨⟩
      NCC.⟦ a -< cs >- ⟧ (fnoc config)
    ∎
  preserves-⊆ (d ⟨ l ∷ r ∷ [] ⟩) config =
      2CC.⟦ translate (d ⟨ l ∷ r ∷ [] ⟩) ⟧ config
    ≡⟨⟩
      2CC.⟦ d ⟨ translate l , translate r ⟩ ⟧ config
    ≡⟨⟩
      2CC.⟦ if config d then translate l else translate r ⟧ config
    ≡⟨ Bool.if-float (λ e → 2CC.⟦ e ⟧ config) (config d) ⟩
      (if config d then 2CC.⟦ translate l ⟧ config else 2CC.⟦ translate r ⟧ config)
    ≡⟨ Eq.cong₂ (if_then_else_ (config d)) (preserves-⊆ l config) (preserves-⊆ r config) ⟩
      (if config d then NCC.⟦ l ⟧ (fnoc config) else NCC.⟦ r ⟧ (fnoc config))
    ≡⟨ lemma ⟩
      Vec.lookup (NCC.⟦ l ⟧ (fnoc config) ∷ NCC.⟦ r ⟧ (fnoc config) ∷ []) (fnoc config d)
    ≡⟨ Vec.lookup-map (fnoc config d) (λ e → NCC.⟦ e ⟧ (fnoc config)) (l ∷ r ∷ []) ⟩
      NCC.⟦ Vec.lookup (l ∷ r ∷ []) (fnoc config d) ⟧ (fnoc config)
    ≡⟨⟩
      NCC.⟦ d ⟨ l ∷ r ∷ [] ⟩ ⟧ (fnoc config)
    ∎
    where
    lemma : ∀ {A : Set} {a b : A} → (if config d then a else b) ≡ Vec.lookup (a ∷ b ∷ []) (fnoc config d)
    lemma with config d
    ... | true = refl
    ... | false = refl

  preserves-⊇ : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
    → (expr : NCC (sucs zero) D i A)
    → NCC.⟦ expr ⟧ ⊆[ conf ] 2CC.⟦ translate expr ⟧
  preserves-⊇ (a -< cs >-) config =
      NCC.⟦ a -< cs >- ⟧ config
    ≡⟨⟩
      artifact a (List.map (λ e → NCC.⟦ e ⟧ config) cs)
    ≡⟨ Eq.cong₂ artifact refl (List.map-cong (λ e → preserves-⊇ e config) cs) ⟩
      artifact a (List.map (λ e → 2CC.⟦ translate e ⟧ (conf config)) cs)
    ≡⟨ Eq.cong₂ artifact refl (List.map-∘ cs) ⟩
      artifact a (List.map (λ e → 2CC.⟦ e ⟧ (conf config)) (List.map translate cs))
    ≡⟨⟩
      2CC.⟦ (a -< List.map translate cs >-) ⟧ (conf config)
    ≡⟨⟩
      2CC.⟦ translate (a -< cs >-) ⟧ (conf config)
    ∎
  preserves-⊇ (d ⟨ l ∷ r ∷ [] ⟩) config =
      NCC.⟦ d ⟨ l ∷ r ∷ [] ⟩ ⟧ config
    ≡⟨⟩
      NCC.⟦ Vec.lookup (l ∷ r ∷ []) (config d) ⟧ config
    ≡⟨ Vec.lookup-map (config d) (λ e → NCC.⟦ e ⟧ config) (l ∷ r ∷ []) ⟨
      Vec.lookup (NCC.⟦ l ⟧ config ∷ NCC.⟦ r ⟧ config ∷ []) (config d)
    ≡⟨ lemma ⟩
      (if conf config d then NCC.⟦ l ⟧ config else NCC.⟦ r ⟧ config)
    ≡⟨ Eq.cong₂ (if_then_else_ (conf config d)) (preserves-⊇ l config) (preserves-⊇ r config) ⟩
      (if conf config d then 2CC.⟦ translate l ⟧ (conf config) else 2CC.⟦ translate r ⟧ (conf config))
    ≡⟨ Bool.if-float (λ e → 2CC.⟦ e ⟧ (conf config)) (conf config d) ⟨
      2CC.⟦ if conf config d then translate l else translate r ⟧ (conf config)
    ≡⟨⟩
      2CC.⟦ d ⟨ translate l , translate r ⟩ ⟧ (conf config)
    ≡⟨⟩
      2CC.⟦ translate (d ⟨ l ∷ r ∷ [] ⟩) ⟧ (conf config)
    ∎
    where
    lemma : {A : Set} → {a b : A} → Vec.lookup (a ∷ b ∷ []) (config d) ≡ (if conf config d then a else b)
    lemma with config d
    ... | zero = refl
    ... | suc zero = refl

  preserves : ∀ {i : Size} {D : 𝔽} {A : 𝔸}
    → (expr : NCC (sucs zero) D i A)
    → 2CC.⟦ translate expr ⟧ ≅[ fnoc ][ conf ] NCC.⟦ expr ⟧
  preserves expr = preserves-⊆ expr and preserves-⊇ expr

  NCC→2CC : ∀ {i : Size} {D : 𝔽} → LanguageCompiler (NCCL {i} (sucs zero) D) (2CCL D)
  NCC→2CC .LanguageCompiler.compile = translate
  NCC→2CC .LanguageCompiler.config-compiler expr .to = conf
  NCC→2CC .LanguageCompiler.config-compiler expr .from = fnoc
  NCC→2CC .LanguageCompiler.preserves expr = ≅[]-sym (preserves expr)


NCC→2CC : ∀ {i : Size} {D : 𝔽} → (n : ℕ≥ 2) → LanguageCompiler (NCCL {i} n D) (2CCL (D × Fin (ℕ≥.toℕ (ℕ≥.pred n))))
NCC→2CC n = NCC→NCC n (sucs zero) ⊕ 2Ary.NCC→2CC

2CC≽NCC : ∀ {D : 𝔽} → (n : ℕ≥ 2) → 2CCL (IndexedDimension D n) ≽ NCCL n D
2CC≽NCC n = expressiveness-from-compiler (NCC→2CC n)
