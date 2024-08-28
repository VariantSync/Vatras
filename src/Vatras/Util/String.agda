module Vatras.Util.String where

open import Data.Bool using (true; false)
open import Data.Char as Char using (Char)
open import Data.Digit using (toDigits; fromDigits; Decimal; Expansion)
open import Data.Empty using (⊥-elim)
open import Data.Fin as Fin using (Fin)
import Data.Fin.Properties as Fin
open import Data.List as List using (List; []; _∷_; _++_)
import Data.List.Properties as List
open import Data.Maybe using (Maybe; nothing; just; maybe′)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _/_; _%_; _≤_; _<_; _≤?_; s≤s)
import Data.Nat.Properties as ℕ
import Data.Nat.Show as ℕ
open import Data.Product using (_×_; _,_; proj₁; proj₂; map₁; map₂; swap)
open import Data.String as String using (String)
open import Function using (id; _∘_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; _≗_; refl)
open import Relation.Nullary.Decidable using (yes; no)

open Eq.≡-Reasoning using (step-≡-⟨; step-≡-⟩; step-≡-∣; _∎)

import Agda.Builtin.Equality.Erase

-- The following axioms are needed to prove properties about string
-- computations but are not yet provided by Agda. See
-- https://github.com/agda/agda/issues/6119 for details.
fromList-toList : ∀ (s : String) → String.fromList (String.toList s) ≡ s
fromList-toList s = Agda.Builtin.Equality.Erase.primEraseEquality trustMe
  where postulate trustMe : _

toList-fromList : ∀ (cs : List Char) → String.toList (String.fromList cs) ≡ cs
toList-fromList cs = Agda.Builtin.Equality.Erase.primEraseEquality trustMe
  where postulate trustMe : _

fromℕ-toℕ : ∀ (c : Char) → Char.fromℕ (Char.toℕ c) ≡ c
fromℕ-toℕ c = Agda.Builtin.Equality.Erase.primEraseEquality trustMe
  where postulate trustMe : _

-- `Char.fromℕ` is only well behaved for unicode code points from the basic
-- plane. Code points in the basic plane are U+0000 - U+D7FF and U+E000 -
-- U+FFFF.  However, we only need the first range so we use a simplified
-- precondition.
toℕ-fromℕ : ∀ (c : ℕ) → c < 0xD7FF → Char.toℕ (Char.fromℕ c) ≡ c
toℕ-fromℕ c p = Agda.Builtin.Equality.Erase.primEraseEquality trustMe
  where postulate trustMe : _


-- Converts the characters '0' to '9' to their equivalent number. Returns
-- `nothing` for any other character.
Char→Decimal : Char → Maybe Decimal
Char→Decimal c with Char.toℕ '0' ≤? Char.toℕ c with Char.toℕ c ≤? Char.toℕ '9'
... | no _    | _       = nothing
... | yes _   | no _    = nothing
... | yes 0≤c | yes c≤9 = just (Fin.fromℕ< {Char.toℕ c ∸ Char.toℕ '0'} (ℕ.+-monoʳ-≤ 1 (ℕ.∸-monoˡ-≤ (Char.toℕ '0') c≤9)))

-- Inverse of `Char→Decimal`
Decimal→Char : Decimal → Char
Decimal→Char d = Char.fromℕ (Fin.toℕ d + Char.toℕ '0')

-- Proof that `Char→Decimal` reverses `Decimal→Char`.
Char→Decimal-Decimal→Char : (d : Decimal) → Char→Decimal (Decimal→Char d) ≡ just d
Char→Decimal-Decimal→Char d with Char.toℕ '0' ≤? Char.toℕ (Decimal→Char d) with Char.toℕ (Decimal→Char d) ≤? Char.toℕ '9'
... | no p    | _       = ⊥-elim (p (ℕ.≤-trans (ℕ.m≤n+m (Char.toℕ '0') (Fin.toℕ d)) (ℕ.≤-reflexive (Eq.sym (toℕ-fromℕ (Fin.toℕ d + (Char.toℕ '0')) (ℕ.m≤n⇒m≤n+o 55236 (s≤s (ℕ.+-monoˡ-≤ (Char.toℕ '0') (Fin.toℕ≤n d)))))))))
... | yes _   | no p    = ⊥-elim (p (ℕ.≤-trans (ℕ.≤-reflexive (toℕ-fromℕ (Fin.toℕ d + (Char.toℕ '0')) (ℕ.m≤n⇒m≤n+o 55236 (s≤s (ℕ.+-monoˡ-≤ (Char.toℕ '0') (Fin.toℕ≤n d)))))) (ℕ.+-monoˡ-≤ (Char.toℕ '0') (ℕ.≤-pred (Fin.toℕ<n d)))))
... | yes 0≤c | yes c≤9 = Eq.cong just (Fin.toℕ-injective (Eq.trans (Fin.toℕ-fromℕ< (ℕ.+-monoʳ-≤ 1 (ℕ.∸-monoˡ-≤ (Char.toℕ '0') c≤9))) (Eq.trans (Eq.cong₂ _∸_ {u = Char.toℕ '0'} (toℕ-fromℕ (Fin.toℕ d + (Char.toℕ '0')) (ℕ.m≤n⇒m≤n+o 55236 (s≤s (ℕ.+-monoˡ-≤ (Char.toℕ '0') (Fin.toℕ≤n d))))) refl) (ℕ.m+n∸n≡m (Fin.toℕ d) (Char.toℕ '0')))))

-- Convert a natural number into a string and join it with another string
-- separated using a '.'.
prependDigits : ℕ → List Char → List Char
prependDigits n cs = List.map Decimal→Char (List.reverse (proj₁ (toDigits 10 n))) ++ ('.' ∷ cs)

-- Parses the digits at the beginning of a string as a natural number and drop
-- the first char after the digits. Inverse of `prependDigits`.
popDigits : List Char → ℕ × List Char
popDigits cs = map₁ fromDigits (go [] cs)
  module popDigits-Implementation where
  go : Expansion 10 → List Char → Expansion 10 × List Char
  go ds [] = ds , []
  go ds (c ∷ cs) = maybe′ (λ d → go (d ∷ ds) cs) (ds , cs) (Char→Decimal c)

-- Proof that `popDigits` reverses `prependDigits`.
popDigits-prependDigits : (n : ℕ) → (cs : List Char) → popDigits (prependDigits n cs) ≡ (n , cs)
popDigits-prependDigits n cs =
  popDigits (prependDigits n cs)
  ≡⟨⟩
    map₁ fromDigits (go [] (prependDigits n cs))
  ≡⟨ Eq.cong₂ map₁ {x = fromDigits} refl (lemma [] (List.reverse (proj₁ (toDigits 10 n)))) ⟩
    map₁ fromDigits (List.reverse (List.reverse (proj₁ (toDigits 10 n))) ++ [] , cs)
  ≡⟨ Eq.cong₂ map₁ {x = fromDigits} refl (Eq.cong₂ _,_ (Eq.cong₂ _++_ (List.reverse-involutive (proj₁ (toDigits 10 n))) refl) refl) ⟩
    map₁ fromDigits (proj₁ (toDigits 10 n) ++ [] , cs)
  ≡⟨ Eq.cong₂ map₁ {x = fromDigits} refl (Eq.cong₂ _,_ (List.++-identityʳ (proj₁ (toDigits 10 n))) refl) ⟩
    map₁ fromDigits (proj₁ (toDigits 10 n) , cs)
  ≡⟨⟩
    fromDigits (proj₁ (toDigits 10 n)) , cs
  ≡⟨ Eq.cong₂ _,_ (proj₂ (toDigits 10 n)) refl ⟩
    n , cs
  ∎
  where
  open popDigits-Implementation (prependDigits n cs)

  -- Induction over the decimal expansion of `n`. The decimal expansion `ds₂` is
  -- actually reversed (most significant digit first) to make the induktion
  -- work.
  lemma : (ds₁ ds₂ : Expansion 10) → go ds₁ (List.map Decimal→Char ds₂ ++ ('.' ∷ cs)) ≡ (List.reverse ds₂ ++ ds₁ , cs)
  lemma ds₁ [] = refl
  lemma ds₁ (d₂ ∷ ds₂) =
      go ds₁ (List.map Decimal→Char (d₂ ∷ ds₂) ++ ('.' ∷ cs))
    ≡⟨⟩
      go ds₁ (Decimal→Char d₂ ∷ (List.map Decimal→Char ds₂ ++ ('.' ∷ cs)))
    ≡⟨⟩
      maybe′ (λ d → go (d ∷ ds₁) (List.map Decimal→Char ds₂ ++ ('.' ∷ cs))) (ds₁ , List.map Decimal→Char ds₂ ++ ('.' ∷ cs)) (Char→Decimal (Decimal→Char d₂))
    ≡⟨ Eq.cong (maybe′ (λ d → go (d ∷ ds₁) (List.map Decimal→Char ds₂ ++ ('.' ∷ cs))) (ds₁ , List.map Decimal→Char ds₂ ++ ('.' ∷ cs))) (Char→Decimal-Decimal→Char d₂) ⟩
      maybe′ (λ d → go (d ∷ ds₁) (List.map Decimal→Char ds₂ ++ ('.' ∷ cs))) (ds₁ , List.map Decimal→Char ds₂ ++ ('.' ∷ cs)) (just d₂)
    ≡⟨⟩
      go (d₂ ∷ ds₁) (List.map Decimal→Char ds₂ ++ ('.' ∷ cs))
    ≡⟨ lemma (d₂ ∷ ds₁) ds₂ ⟩
      List.reverse ds₂ ++ (d₂ ∷ ds₁) , cs
    ≡⟨ Eq.cong₂ _,_ (List.ʳ++-defn ds₂) refl ⟨
      ds₂ List.ʳ++ (d₂ ∷ ds₁) , cs
    ≡⟨⟩
      (d₂ ∷ ds₂) List.ʳ++ ds₁ , cs
    ≡⟨ Eq.cong₂ _,_ (List.ʳ++-defn (d₂ ∷ ds₂)) refl ⟩
      List.reverse (d₂ ∷ ds₂) ++ ds₁ , cs
    ∎

-- The `diagonal-*` functions convert between a string and a number and the
-- string with the number and a '.' prepended.
-- Example:
-- diagonal-ℕ ("asd" , 123) ≡ "123.asd"
-- diagonal-ℕ⁻¹ "123.asd" ≡ ("asd" , 123)
--
-- These functions are an example implementation of the requirements of
-- `Translation.LanguageMap.Expressiveness` for `String`. They are called
-- diagonal because they are an instance of how to encode a pair of numbers (two
-- bit streams) into a single number (bit streams) using the scheme used in
-- diagonal arguments.
diagonal-ℕ : String × ℕ → String
diagonal-ℕ (s , n) = String.fromList (prependDigits n (String.toList s))

diagonal-ℕ⁻¹ : String → String × ℕ
diagonal-ℕ⁻¹ s = swap (map₂ String.fromList (popDigits (String.toList s)))

diagonal-ℕ-proof : diagonal-ℕ⁻¹ ∘ diagonal-ℕ ≗ id
diagonal-ℕ-proof (s , n) =
    diagonal-ℕ⁻¹ (diagonal-ℕ (s , n))
  ≡⟨⟩
    swap (map₂ String.fromList (popDigits (String.toList (String.fromList (prependDigits n (String.toList s))))))
  ≡⟨ Eq.cong swap (Eq.cong₂ map₂ {x = String.fromList} refl (Eq.cong popDigits (toList-fromList (prependDigits n (String.toList s))))) ⟩
    swap (map₂ String.fromList (popDigits (prependDigits n (String.toList s))))
  ≡⟨ Eq.cong swap (Eq.cong₂ map₂ {x = String.fromList} refl (popDigits-prependDigits n (String.toList s))) ⟩
    swap (map₂ String.fromList (n , String.toList s))
  ≡⟨⟩
    swap (n , String.fromList (String.toList s))
  ≡⟨⟩
    (String.fromList (String.toList s) , n )
  ≡⟨ Eq.cong₂ _,_ (fromList-toList s) refl ⟩
    s , n
  ∎
