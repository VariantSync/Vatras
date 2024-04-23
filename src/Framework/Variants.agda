{-# OPTIONS --allow-unsolved-metas #-}

module Framework.Variants where

open import Data.Unit using (⊤; tt)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.List as List using (List; []; _∷_; map)
open import Function using (id; _∘_; flip)
open import Size using (Size; ↑_; ∞)
import Level

open import Framework.Definitions using (𝕍; 𝔸; atoms)
open import Framework.VariabilityLanguage
open import Construct.Artifact as At using (_-<_>-; map-children) renaming (Syntax to Artifact; Construct to ArtifactC)

open import Data.EqIndexedSet

-- Induction principle for `Variant`
open import Induction as Induction using (RecStruct; RecursorBuilder; Recursor)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
import Data.List.Relation.Unary.All.Properties as All
import Data.List.Properties as List
open import Relation.Binary.PropositionalEquality as Eq using (_≡_)
open import Relation.Unary using (_⊆′_)

VariantRecStruct : ∀ ℓ A → RecStruct (Variant A) ℓ ℓ
VariantRecStruct ℓ A P (artifact a cs) = All P cs

VariantRecusorBuilder : ∀ {ℓ} (A : 𝔸) → RecursorBuilder (VariantRecStruct ℓ A)
VariantRecusorBuilder {ℓ} A P vRecStruct⊆'P (artifact a cs) = go cs
  module VariantRecusorBuilder-Implementation where
  go : (cs' : List (Variant A)) → All P cs'
  go [] = []
  go (c ∷ cs') = vRecStruct⊆'P c (VariantRecusorBuilder A P vRecStruct⊆'P c) ∷ go cs'

VariantInduction : ∀ {ℓ} {A : 𝔸} → Recursor (VariantRecStruct ℓ A)
VariantInduction {A = A} = Induction.build (VariantRecusorBuilder A)

foldVariant : ∀ {ℓ} {A : 𝔸} {R : Set ℓ} → (atoms A → List R → R) → Variant A → R
foldVariant {ℓ} {A} {R} f = VariantInduction (λ _ → R) foldStep
  module foldVariant-Implementation where
  foldStep : VariantRecStruct ℓ A (λ _ → R) ⊆′ (λ _ → R)
  foldStep (artifact a cs) ih = f a (All.reduce id ih)

foldVariant-reduction : ∀ {ℓ} {A : 𝔸} {R : Set ℓ}
  → (f : atoms A → List R → R)
  → {a : atoms A}
  → {cs : List (Variant A)}
  → foldVariant f (artifact a cs) ≡ f a (map (foldVariant f) cs)
foldVariant-reduction {A = A} {R} f {a} {cs} =
  begin
    foldVariant f (artifact a cs)
  ≡⟨⟩
    VariantInduction (λ _ → R) foldStep (artifact a cs)
  ≡⟨⟩
    Induction.build (VariantRecusorBuilder A) (λ _ → R) foldStep (artifact a cs)
  ≡⟨⟩
    f a (All.reduce id (VariantRecusorBuilder A (λ _ → R) foldStep (artifact a cs)))
  ≡⟨⟩
    f a (All.reduce id (go cs))
  ≡⟨ Eq.cong (f a) (lemma cs) ⟩
    f a (map (Induction.build (VariantRecusorBuilder A) (λ _ → R) foldStep) cs)
  ≡⟨⟩
    f a (map (VariantInduction (λ _ → R) foldStep) cs)
  ≡⟨⟩
    f a (map (foldVariant f) cs)
  ∎
  where
  open Eq.≡-Reasoning
  open foldVariant-Implementation f
  open VariantRecusorBuilder-Implementation A (λ _ → R) foldStep a cs

  lemma :
      (cs' : List (Variant A))
    → All.reduce id (go cs') ≡ map (Induction.build (VariantRecusorBuilder A) (λ _ → R) foldStep) cs'
  lemma [] = Eq.refl
  lemma (c ∷ cs') = Eq.cong₂ _∷_ Eq.refl (lemma cs')


data GrulerVariant : 𝕍 where
  asset : ∀ {A : 𝔸} (a : atoms A) → GrulerVariant A
  _∥_   : ∀ {A : 𝔸} (l : GrulerVariant A) → (r : GrulerVariant A) → GrulerVariant A

data Rose : Size → 𝕍 where
  rose : ∀ {i} {A : 𝔸} → Artifact (Rose i) A → Rose (↑ i) A

rose-leaf : ∀ {A : 𝔸} → atoms A → Rose ∞ A
rose-leaf {A} a = rose (At.leaf a)

-- Variants are also variability languages
Variant-is-VL : VariabilityLanguage
Variant-is-VL = ⟪ Variant , ⊤ , (λ e c → e) ⟫

open import Framework.Construct
open import Data.Maybe using (nothing; just)
open import Relation.Binary.PropositionalEquality as Peq using (_≡_; _≗_; refl)
open Peq.≡-Reasoning

Artifact∈ₛVariant : Artifact ∈ₛ Variant
cons Artifact∈ₛVariant (a -< cs >-) = artifact a cs
snoc Artifact∈ₛVariant (artifact a cs) = just (a -< cs >-)
id-l Artifact∈ₛVariant (a -< cs >-) = refl

Artifact∈ₛRose : Artifact ∈ₛ Rose ∞
cons Artifact∈ₛRose x = rose x
snoc Artifact∈ₛRose (rose x) = just x
id-l Artifact∈ₛRose x = refl

-- GrulerVL : VariabilityLanguage GrulerVariant
-- GrulerVL = Variant-is-VL GrulerVariant

RoseVL : VariabilityLanguage
RoseVL = ⟪ Rose ∞ , ⊤ , ⟦_⟧ ⟫
  where
  ⟦_⟧ : {A : 𝔸} → Rose ∞ A → ⊤ → Variant A
  ⟦ rose (a -< cs >-) ⟧ tt = go a cs []
    where
    go : {A : 𝔸} → atoms A → List (Rose ∞ A) → List (Variant A) → Variant A
    go a [] vs = artifact a (List.reverse vs)
    go a (c ∷ cs) vs = go a cs (⟦ c ⟧ tt ∷ vs)

open import Data.String using (String; _++_; intersperse)
show-rose : ∀ {i} {A} → (atoms A → String) → Rose i A → String
show-rose show-a (rose (a -< [] >-)) = show-a a
show-rose show-a (rose (a -< es@(_ ∷ _) >-)) = show-a a ++ "-<" ++ (intersperse ", " (map (show-rose show-a) es)) ++ ">-"

show-variant : ∀ {A} → (atoms A → String) → Variant A → String
show-variant {A} show-a = foldVariant go
  where
  go : atoms A → List String → String
  go a [] = show-a a
  go a es@(_ ∷ _) = show-a a ++ "-<" ++ (intersperse ", " es) ++ ">-"


-- Variants can be encoded into other variability language.
-- The result is an expression which cannot be configured
-- (i.e., configurations don't matter because there is only
-- a single variant anyway).

open import Framework.Compiler using (LanguageCompiler)
open LanguageCompiler

VariantEncoder : ∀ (Γ : VariabilityLanguage) → Set₁
VariantEncoder Γ = LanguageCompiler Variant-is-VL Γ


module _ (A : 𝔸) {Γ : VariabilityLanguage} (encoder : VariantEncoder Γ) where
  open import Data.EqIndexedSet

  private
    ⟦_⟧ = Semantics Γ
    ⟦_⟧ᵥ = Semantics Variant-is-VL

  encoded-variant-is-singleton-set :
    ∀ (v : Variant A) → Singleton ⟦ compile encoder v ⟧
  encoded-variant-is-singleton-set v = v , λ c → proj₂ (preserves encoder v) c

  encode-idemp : ∀ (c : Config Γ) (v : Variant A)
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

-- rose-encoder :
--   ∀ (Γ : VariabilityLanguage)
--   → ArtifactC ⟦∈⟧ₚ Γ
--   → Config Γ
--   → VariantEncoder Γ
-- rose-encoder Γ has c = record
--   { compile = t
--   ; config-compiler = λ _ → record { to = confi; from = fnoci }
--   ; preserves = p
--   }
--   where
--     ⟦_⟧ = Semantics Γ
--     ⟦_⟧ᵥ = Semantics Variant-is-VL

--     confi : ⊤ → Config Γ
--     confi tt = c

--     fnoci : Config Γ → ⊤
--     fnoci _ = tt

--     ppp : toVariational ArtifactC (C∈ₛV has) ⟦∈⟧ᵥ Γ
--     ppp = ⟦∈⟧ₚ→⟦∈⟧ᵥ has

--     module _ {A : 𝔸} where
--       t : ∀ {i} → Variant A → Expression Γ A
--       t (artifact a cs) = cons (C∈ₛΓ has) (a -< List.map t cs >-)

--       ⟦_⟧ₚ : ∀ {A}
--         → (e : Artifact (Expression Γ) A)
--         → (c : Config Γ)
--         → Artifact Variant A
--       ⟦_⟧ₚ = pcong ArtifactC Γ

--       h : ∀ (v : Variant A) (j : Config Γ) → ⟦ t v ⟧ j ≡ v
--       h (artifact a cs) j =
--         begin
--           ⟦ cons (C∈ₛΓ has) (map-children t (a -< cs >-)) ⟧ j
--         ≡⟨ resistant has (map-children t (a -< cs >-)) j ⟩
--           (cons (C∈ₛV has) ∘ ⟦ map-children t (a -< cs >-)⟧ₚ) j
--         ≡⟨⟩
--           cons (C∈ₛV has) (⟦ map-children t (a -< cs >-) ⟧ₚ j)
--         ≡⟨⟩
--           (cons (C∈ₛV has) ∘ flip ⟦_⟧ₚ j) (map-children t (a -< cs >-))
--         ≡⟨⟩
--           (cons (C∈ₛV has) ∘ flip ⟦_⟧ₚ j) (a -< map t cs >-)
--         -- ≡⟨ Peq.cong (cons (C∈ₛV has) ∘ flip ⟦_⟧ₚ j) (Peq.cong (a -<_>-) {!!}) ⟩
--           -- (cons (C∈ₛV has) ∘ flip ⟦_⟧ₚ j) (a -< cs >-)
--         ≡⟨ {!!} ⟩
--         -- ≡⟨ bar _ ⟩
--           -- rose            (pcong ArtifactC Γ (a -< map t cs >-) j)
--         -- ≡⟨ Peq.cong rose {!preservation ppp (a -< map t cs >-)!} ⟩
--           rose (a -< cs >-)
--         ∎
--         where
--           module _ where
--             open import Data.Maybe using (just; nothing)
--             co = cons (C∈ₛV has)
--             oc = snoc (C∈ₛV has)

--             -- unprovable
--             -- Imagine our domain A is pairs (a , b)
--             -- Then cons could take an '(a , b) -< cs >-'
--             -- and encode it as a 'rose ((b , a) -< cs >-)'
--             -- for which exists an inverse snoc that just has
--             -- to swap the arguments in the pair again.
--             -- So we need a stronger axiom here that syntax
--             -- and not just information is retained???
--             bar : co ≗ rose
--             bar x with co x in eq
--             ... | rose y = {!!}

--             sno : oc ∘ rose ≗ just
--             sno a rewrite Peq.sym (bar a) = id-l (C∈ₛV has) a

--             foo : co (a -< cs >-) ≡ rose (a -< cs >-)
--             foo = bar (a -< cs >-)

--       -- lp : ∀ (e : Variant A) → ⟦ e ⟧ᵥ ⊆[ confi ] ⟦ t e ⟧
--       -- lp (rose x) i =
--       --   begin
--       --     ⟦ rose x ⟧ᵥ i
--       --   ≡⟨⟩
--       --     rose x
--       --   ≡⟨ {!!} ⟩
--       --     (cons (C∈ₛV has) ∘ pcong ArtifactC Γ (map-children t x)) (confi i)
--       --   ≡⟨ resistant has (map-children t x) (confi i) ⟨
--       --     ⟦ cons (C∈ₛΓ has) (map-children t x) ⟧ (confi i)
--       --   ∎

--       p : ∀ (e : Variant A) → ⟦ e ⟧ᵥ ≅[ confi ][ fnoci ] ⟦ t e ⟧
--       -- p (rose x) = {!!}
--       p e = irrelevant-index-≅ e (λ _ → refl) (λ j → h e j) confi fnoci
