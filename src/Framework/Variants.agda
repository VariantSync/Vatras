{-# OPTIONS --allow-unsolved-metas #-}

module Framework.Variants where

open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List using (List; []; _∷_; map)
open import Function using (id; _∘_; flip)
open import Size using (Size; ↑_; ∞)

open import Framework.Definitions using (𝕍; 𝔸; atoms)
open import Framework.VariabilityLanguage
open import Construct.Artifact as At using (map-children) renaming (Syntax to Artifact; Construct to ArtifactC)

open import Data.EqIndexedSet

data GrulerVariant (A : 𝔸) : Set where
  asset : (a : atoms A) → GrulerVariant A
  _∥_   : (l : GrulerVariant A) → (r : GrulerVariant A) → GrulerVariant A

iflip : ∀ {a c} {A : Set a} {C : A → Size → Set c}
  → ((x : A) (y : Size) → C x y)
  → ((y : Size) (x : A) → C x y)
iflip cons y x = cons x y

data Rose (A : 𝔸) : Size → Set where
  rose : ∀ {i} → Artifact (iflip Rose i) A → Rose A (↑ i)

rose-leaf : ∀ {A : 𝔸} → atoms A → Rose A ∞
rose-leaf {A} a = rose (At.leaf a)

pattern _-<_>- a cs = rose (a At.-< cs >-)

-- Variants are also variability languages
Variant-is-VL : ∀ (V : 𝕍) → VariabilityLanguage V
Variant-is-VL V = ⟪ V , ⊤ , (λ e c → e) ⟫

open import Framework.Construct
open import Data.Maybe using (nothing; just)
open import Relation.Binary.PropositionalEquality as Peq using (_≡_; _≗_; refl)
open Peq.≡-Reasoning

children-equality : ∀ {A : 𝔸} {a₁ a₂ : atoms A} {cs₁ cs₂ : List (Rose A ∞)} → a₁ -< cs₁ >- ≡ a₂ -< cs₂ >- → cs₁ ≡ cs₂
children-equality refl = refl

Artifact∈ₛRose : Artifact ∈ₛ iflip Rose ∞
cons Artifact∈ₛRose x = rose x
snoc Artifact∈ₛRose (rose x) = just x
id-l Artifact∈ₛRose x = refl

GrulerVL : VariabilityLanguage GrulerVariant
GrulerVL = Variant-is-VL GrulerVariant

RoseVL : VariabilityLanguage (iflip Rose ∞)
RoseVL = Variant-is-VL (iflip Rose ∞)

open import Data.String using (String; _++_; intersperse)
show-rose : ∀ {i} {A} → (atoms A → String) → Rose A i → String
show-rose show-a (a -< [] >-) = show-a a
show-rose show-a (a -< es@(_ ∷ _) >-) = show-a a ++ "-<" ++ (intersperse ", " (map (show-rose show-a) es)) ++ ">-"


-- Variants can be encoded into other variability language.
-- The result is an expression which cannot be configured
-- (i.e., configurations don't matter because there is only
-- a single variant anyway).

open import Framework.Compiler using (LanguageCompiler)
open LanguageCompiler

VariantEncoder : ∀ (V : 𝕍) (Γ : VariabilityLanguage V) → Set₁
VariantEncoder V Γ = LanguageCompiler (Variant-is-VL V) Γ


module _ (V : 𝕍) (A : 𝔸) {Γ : VariabilityLanguage V} (encoder : VariantEncoder V Γ) where
  open import Data.EqIndexedSet

  private
    ⟦_⟧ = Semantics Γ
    ⟦_⟧ᵥ = Semantics (Variant-is-VL V)

  encoded-variant-is-singleton-set :
    ∀ (v : V A) → Singleton ⟦ compile encoder v ⟧
  encoded-variant-is-singleton-set v = v , λ c → proj₂ (preserves encoder v) c

  encode-idemp : ∀ (c : Config Γ) (v : V A)
    → ⟦ compile encoder v ⟧ c ≡ v
  encode-idemp c v =
    begin
      ⟦ compile encoder v ⟧ c
    ≡⟨ irrelevant-index (encoded-variant-is-singleton-set v) ⟩
      ⟦ compile encoder v ⟧ (conf encoder v tt)
    ≡⟨ proj₁ (preserves encoder v) tt ⟨
      ⟦ v ⟧ᵥ tt
    ≡⟨⟩
      v
    ∎

rose-encoder :
  ∀ (Γ : VariabilityLanguage (iflip Rose ∞))
  → ArtifactC ⟦∈⟧ₚ Γ
  → Config Γ
  → VariantEncoder (iflip Rose ∞) Γ
rose-encoder Γ has c = record
  { compile = t
  ; config-compiler = λ _ → record { to = confi; from = fnoci }
  ; preserves = p
  }
  where
    ⟦_⟧ = Semantics Γ
    ⟦_⟧ᵥ = Semantics (Variant-is-VL (iflip Rose ∞))

    confi : ⊤ → Config Γ
    confi tt = c

    fnoci : Config Γ → ⊤
    fnoci _ = tt

    ppp : toVariational ArtifactC (C∈ₛV has) ⟦∈⟧ᵥ Γ
    ppp = ⟦∈⟧ₚ→⟦∈⟧ᵥ has

    module _ {A : 𝔸} where
      t : ∀ {i} → Rose A i → Expression Γ A
      t (rose x) = cons (C∈ₛΓ has) (map-children t x)

      ⟦_⟧ₚ : ∀ {A}
        → (e : Artifact (Expression Γ) A)
        → (c : Config Γ)
        → Artifact (iflip Rose ∞) A
      ⟦_⟧ₚ = pcong ArtifactC Γ

      h : ∀ (v : Rose A ∞) (j : Config Γ) → ⟦ t v ⟧ j ≡ v
      h (rose (a At.-< cs >-)) j =
        begin
          ⟦ cons (C∈ₛΓ has) (map-children t (a At.-< cs >-)) ⟧ j
        ≡⟨ resistant has (map-children t (a At.-< cs >-)) j ⟩
          (cons (C∈ₛV has) ∘ ⟦ map-children t (a At.-< cs >-)⟧ₚ) j
        ≡⟨⟩
          cons (C∈ₛV has) (⟦ map-children t (a At.-< cs >-) ⟧ₚ j)
        ≡⟨⟩
          (cons (C∈ₛV has) ∘ flip ⟦_⟧ₚ j) (map-children t (a At.-< cs >-))
        ≡⟨⟩
          (cons (C∈ₛV has) ∘ flip ⟦_⟧ₚ j) (a At.-< map t cs >-)
        -- ≡⟨ Peq.cong (cons (C∈ₛV has) ∘ flip ⟦_⟧ₚ j) (Peq.cong (a At.-<_>-) {!!}) ⟩
          -- (cons (C∈ₛV has) ∘ flip ⟦_⟧ₚ j) (a At.-< cs >-)
        ≡⟨ {!!} ⟩
        -- ≡⟨ bar _ ⟩
          -- rose            (pcong ArtifactC Γ (a At.-< map t cs >-) j)
        -- ≡⟨ Peq.cong rose {!preservation ppp (a At.-< map t cs >-)!} ⟩
          rose (a At.-< cs >-)
        ∎
        where
          module _ where
            open import Data.Maybe using (just; nothing)
            co = cons (C∈ₛV has)
            oc = snoc (C∈ₛV has)

            -- unprovable
            -- Imagine our domain A is pairs (a , b)
            -- Then cons could take an '(a , b) At.-< cs >-'
            -- and encode it as a 'rose ((b , a) At.-< cs >-)'
            -- for which exists an inverse snoc that just has
            -- to swap the arguments in the pair again.
            -- So we need a stronger axiom here that syntax
            -- and not just information is retained???
            bar : co ≗ rose
            bar x with co x in eq
            ... | rose y = {!!}

            sno : oc ∘ rose ≗ just
            sno a rewrite Peq.sym (bar a) = id-l (C∈ₛV has) a

            foo : co (a At.-< cs >-) ≡ rose (a At.-< cs >-)
            foo = bar (a At.-< cs >-)

      -- lp : ∀ (e : Rose ∞ A) → ⟦ e ⟧ᵥ ⊆[ confi ] ⟦ t e ⟧
      -- lp (rose x) i =
      --   begin
      --     ⟦ rose x ⟧ᵥ i
      --   ≡⟨⟩
      --     rose x
      --   ≡⟨ {!!} ⟩
      --     (cons (C∈ₛV has) ∘ pcong ArtifactC Γ (map-children t x)) (confi i)
      --   ≡⟨ resistant has (map-children t x) (confi i) ⟨
      --     ⟦ cons (C∈ₛΓ has) (map-children t x) ⟧ (confi i)
      --   ∎

      p : ∀ (e : Rose A ∞) → ⟦ e ⟧ᵥ ≅[ confi ][ fnoci ] ⟦ t e ⟧
      -- p (rose x) = {!!}
      p e = irrelevant-index-≅ e (λ _ → refl) (λ j → h e j) confi fnoci
