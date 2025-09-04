open import Vatras.Framework.Definitions using (𝔽; 𝔸; atoms)
open import Relation.Binary using (DecidableEquality)
module Vatras.Lang.OC.DeadElim (F : 𝔽) (_≟_ : DecidableEquality F) where

open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.Empty using (⊥-elim)
open import Data.List as List using (List; []; _∷_)
import Data.List.Properties as List
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.List.Membership.DecPropositional _≟_ using (_∈_; _∉_; _∈?_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂)
open import Function using (id)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≢_)
open import Relation.Nullary.Decidable using (yes; no; decidable-stable)
open import Size using (Size; ∞)

open import Vatras.Util.AuxProofs using (true≢false; if-idemp)
import Vatras.Util.List as List
open import Vatras.Data.EqIndexedSet using (_≅[_][_]_; ≗→≅[]; _≅_; _⊆_)
open import Vatras.Framework.Variants using (_-<_>-)
open import Vatras.Lang.OC F using (OC; _-<_>-; _❲_❳; Configuration; ⟦_⟧ₒ)
open import Vatras.Lang.OC.Util using (all-oc)

data RestrictOptions {A : 𝔸} : {i : Size} → List F → OC i A → Set₁ where
  _-<_>- : ∀ {i} → {a : atoms A} → {cs : List (OC i A)} → (env : List F) → All (RestrictOptions env) cs → RestrictOptions env (a -< cs >-)
  _❲_❳ : ∀ {i} → {f : F} → {c : OC i A} → {env : List F} → f ∉ env → RestrictOptions (f ∷ env) c → RestrictOptions env (f ❲ c ❳)

data Undead {A : 𝔸} : {i : Size} → OC i A → Set₁ where
  undead : {i : Size} → {env : List F} → {e : OC i A} → RestrictOptions env e → Undead e

elimDead' : {i : Size} → {A : 𝔸} → (env : List F) → OC i A → Σ (OC ∞ A) (RestrictOptions env)
elimDead' env (a -< cs >-) = a -< List.map proj₁ (List.map (elimDead' env) cs) >- , (env -< All.fromList (List.map (elimDead' env) cs) >-)
elimDead' env (a ❲ c ❳) with a ∈? env
elimDead' env (a ❲ c ❳) | yes a∈env = elimDead' env c
elimDead' env (a ❲ c ❳) | no a∉env = a ❲ proj₁ (elimDead' (a ∷ env) c) ❳ , a∉env ❲ proj₂ (elimDead' (a ∷ env) c) ❳

elimDead : {i : Size} → {A : 𝔸} → OC i A → OC ∞ A
elimDead e = proj₁ (elimDead' [] e)

elimDead-preserves' : {i : Size} → {A : 𝔸} → (env : List F) → (e : OC i A) → (c : Configuration) → All (λ f → c f ≡ true) env → ⟦ proj₁ (elimDead' env e) ⟧ₒ c ≡ ⟦ e ⟧ₒ c
elimDead-preserves' env (a -< cs >-) c c-env≡true =
    ⟦ proj₁ (elimDead' env (a -< cs >-)) ⟧ₒ c
  ≡⟨⟩
    ⟦ a -< List.map proj₁ (List.map (elimDead' env) cs) >- ⟧ₒ c
  ≡⟨⟩
    just (a -< List.catMaybes (List.map (λ e → ⟦ e ⟧ₒ c) (List.map proj₁ (List.map (elimDead' env) cs))) >-)
  ≡⟨ Eq.cong (λ e → just (a -< List.catMaybes e >-)) (List.map-∘ (List.map (elimDead' env) cs)) ⟨
    just (a -< List.catMaybes (List.map (λ e → ⟦ proj₁ e ⟧ₒ c) (List.map (elimDead' env) cs)) >-)
  ≡⟨ Eq.cong (λ e → just (a -< List.catMaybes e >-)) (List.map-∘ cs) ⟨
    just (a -< List.catMaybes (List.map (λ e → ⟦ proj₁ (elimDead' env e) ⟧ₒ c) cs) >-)
  ≡⟨ Eq.cong (λ e → just (a -< List.catMaybes e >-)) (List.map-cong (λ e → elimDead-preserves' env e c c-env≡true) cs) ⟩
    just (a -< List.catMaybes (List.map (λ e → ⟦ e ⟧ₒ c) cs) >-)
  ≡⟨⟩
    ⟦ a -< cs >- ⟧ₒ c
  ∎
  where
  open Eq.≡-Reasoning
elimDead-preserves' env (a ❲ e ❳) c c-env≡true with a ∈? env
elimDead-preserves' env (a ❲ e ❳) c c-env≡true | yes a∈env with c a in c-a
elimDead-preserves' env (a ❲ e ❳) c c-env≡true | yes a∈env | true = elimDead-preserves' env e c c-env≡true
elimDead-preserves' env (a ❲ e ❳) c c-env≡true | yes a∈env | false = ⊥-elim (true≢false (All.lookup c-env≡true a∈env) c-a)
elimDead-preserves' env (a ❲ e ❳) c c-env≡true | no a∉env with c a in c-a
elimDead-preserves' env (a ❲ e ❳) c c-env≡true | no a∉env | true = elimDead-preserves' (a ∷ env) e c (c-a ∷ c-env≡true)
elimDead-preserves' env (a ❲ e ❳) c c-env≡true | no a∉env | false = Eq.refl

elimDead-preserves : {i : Size} → {A : 𝔸} → (e : OC i A) → ⟦ elimDead e ⟧ₒ ≅[ id ][ id ] ⟦ e ⟧ₒ
elimDead-preserves e = ≗→≅[] (λ c → elimDead-preserves' [] e c [])

-- TODO WFOC

undead→≢ : {i : Size} → {A : 𝔸} → {f₁ f₂ : F} → {e : OC i A} → Undead (f₁ ❲ f₂ ❲ e ❳ ❳) → f₁ ≢ f₂
undead→≢ (undead (f₁∉env ❲ f₂∉env ❲ undead-e ❳ ❳)) f₁≡f₂ = f₂∉env (here (Eq.sym f₁≡f₂))

changeConfig : F → Bool → Configuration → Configuration
changeConfig f₁ b c f₂ with f₁ ≟ f₂
changeConfig f₁ b c f₂ | yes f₁≡f₂ = b
changeConfig f₁ b c f₂ | no f₁≢f₂ = c f₂

changeConfig-≡ : (f : F) → (b : Bool) → (c : Configuration) → changeConfig f b c f ≡ b
changeConfig-≡ f b c with f ≟ f
changeConfig-≡ f b c | yes f≡f = Eq.refl
changeConfig-≡ f b c | no f≢f = ⊥-elim (f≢f Eq.refl)

changeConfig-≢ : {f₁ f₂ : F} → (b : Bool) → f₁ ≢ f₂ → (c : Configuration) → changeConfig f₁ b c f₂ ≡ c f₂
changeConfig-≢ {f₁} {f₂} b f₁≢f₂ c with f₁ ≟ f₂
changeConfig-≢ {f₁} {f₂} b f₁≢f₂ c | yes f₁≡f₂ = ⊥-elim (f₁≢f₂ f₁≡f₂)
changeConfig-≢ {f₁} {f₂} b f₁≢f₂ c | no f₁≢f₂ = Eq.refl

changeConfig-∉ : {i : Size} → {A : 𝔸} → {env : List F} → (f : F) → (f ∈ env) → (b : Bool) → (c : Configuration) → (e : OC i A) → RestrictOptions env e → ⟦ e ⟧ₒ (changeConfig f b c) ≡ ⟦ e ⟧ₒ c
changeConfig-∉ f f∈env b c (a -< cs >-) (env -< undead-e >-) =
    ⟦ a -< cs >- ⟧ₒ (changeConfig f b c)
  ≡⟨⟩
    just (a -< List.catMaybes (List.map (λ e → ⟦ e ⟧ₒ (changeConfig f b c)) cs) >-)
  ≡⟨ Eq.cong (λ x → just (a -< List.catMaybes x >-)) (List.map-cong-with∈ cs (λ e e∈cs → changeConfig-∉ f f∈env b c e (All.lookup undead-e e∈cs))) ⟩
    just (a -< List.catMaybes (List.map (λ e → ⟦ e ⟧ₒ c) cs) >-)
  ≡⟨⟩
    ⟦ a -< cs >- ⟧ₒ c
  ∎
  where
  open Eq.≡-Reasoning
changeConfig-∉ f f∈env b c (f' ❲ e ❳) undead-e with f ≟ f'
changeConfig-∉ {env = env} f f∈env b c (f' ❲ e ❳) (f'∉env ❲ undead-e ❳) | yes f≡f' = ⊥-elim (f'∉env (Eq.subst (_∈ env) f≡f' f∈env))
changeConfig-∉ f f∈env b c (f' ❲ e ❳) (f'∉env ❲ undead-e ❳) | no f≢f' = Eq.cong (λ e → if c f' then e else nothing) (changeConfig-∉ f (there f∈env) b c e undead-e)

eval-option : {i : Size} → {A : 𝔸} → {f : F} → {e : OC i A} → Undead (f ❲ e ❳) → (c : Configuration) → ⟦ f ❲ e ❳ ⟧ₒ (changeConfig f true c) ≡ ⟦ e ⟧ₒ c
eval-option {f = f} {e = e} (undead (_ ❲ undead-e ❳)) c =
    ⟦ f ❲ e ❳ ⟧ₒ (changeConfig f true c)
  ≡⟨⟩
    (if changeConfig f true c f then ⟦ e ⟧ₒ (changeConfig f true c) else nothing)
  ≡⟨ Eq.cong (λ b → if b then ⟦ e ⟧ₒ (changeConfig f true c) else nothing) (changeConfig-≡ f true c) ⟩
    ⟦ e ⟧ₒ (changeConfig f true c)
  ≡⟨ changeConfig-∉ f (here Eq.refl) true c e undead-e ⟩
    ⟦ e ⟧ₒ c
  ∎
  where
  open Eq.≡-Reasoning

join-options : {i : Size} → {A : 𝔸} → (f₁ f₂ : F) → (e : OC i A) → Undead (f₁ ❲ f₂ ❲ e ❳ ❳) → ⟦ f₁ ❲ f₂ ❲ e ❳ ❳ ⟧ₒ ≅ ⟦ f₂ ❲ e ❳ ⟧ₒ
join-options f₁ f₂ e undead-e'@(undead (f₁∉env ❲ f₂∉env ❲ undead-e ❳ ❳)) = go-⊆ , go-⊇
  where
  go-⊆ : ⟦ f₁ ❲ f₂ ❲ e ❳ ❳ ⟧ₒ ⊆ ⟦ f₂ ❲ e ❳ ⟧ₒ
  go-⊆ c with c f₂ in c-f₂
  go-⊆ c | false = c , (
      (if c f₁ then nothing else nothing)
    ≡⟨ if-idemp (c f₁) ⟩
      nothing
    ≡⟨ Eq.cong (λ b → if b then ⟦ e ⟧ₒ c else nothing) c-f₂ ⟨
      (if c f₂ then ⟦ e ⟧ₒ c else nothing)
    ∎)
    where
    open Eq.≡-Reasoning
  go-⊆ c | true with c f₁
  go-⊆ c | true | false = all-oc false , Eq.refl
  go-⊆ c | true | true = c , (
      ⟦ e ⟧ₒ c
    ≡⟨ Eq.cong (λ b → if b then ⟦ e ⟧ₒ c else nothing) c-f₂ ⟨
      (if c f₂ then ⟦ e ⟧ₒ c else nothing)
    ∎)
    where
    open Eq.≡-Reasoning

  go-⊇ : ⟦ f₂ ❲ e ❳ ⟧ₒ ⊆ ⟦ f₁ ❲ f₂ ❲ e ❳ ❳ ⟧ₒ
  go-⊇ c with c f₂ in c-f₂
  go-⊇ c | false = all-oc false , Eq.refl
  go-⊇ c | true = changeConfig f₁ true c , (
      ⟦ e ⟧ₒ c
    ≡⟨ changeConfig-∉ f₁ (there (here Eq.refl)) true c e undead-e ⟨
      ⟦ e ⟧ₒ (changeConfig f₁ true c)
    ≡⟨ Eq.cong (λ b → if b then ⟦ e ⟧ₒ (changeConfig f₁ true c) else nothing) c-f₂ ⟨
      (if c f₂
        then ⟦ e ⟧ₒ (changeConfig f₁ true c)
        else nothing)
    ≡⟨ Eq.cong (λ b → if b then ⟦ e ⟧ₒ (changeConfig f₁ true c) else nothing) (changeConfig-≢ true (undead→≢ undead-e') c) ⟨
      (if changeConfig f₁ true c f₂
        then ⟦ e ⟧ₒ (changeConfig f₁ true c)
        else nothing)
    ≡⟨ Eq.cong (λ b → if b then if changeConfig f₁ true c f₂ then ⟦ e ⟧ₒ (changeConfig f₁ true c) else nothing else nothing) (changeConfig-≡ f₁ true c) ⟨
      (if changeConfig f₁ true c f₁
        then if changeConfig f₁ true c f₂
          then ⟦ e ⟧ₒ (changeConfig f₁ true c)
          else nothing
        else nothing)
    ∎)
    where
    open Eq.≡-Reasoning
