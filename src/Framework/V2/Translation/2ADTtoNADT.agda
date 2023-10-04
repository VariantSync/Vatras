module Framework.V2.Translation.2ADTtoNADT where

open import Data.Nat using (ℕ)

open import Framework.V2.Definitions

open import Framework.V2.Lang.2ADT
open import Framework.V2.Lang.NADT

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
