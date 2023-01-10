module State where

open import Data.Product using (_×_; proj₁; proj₂)

open import Effect.Functor using (RawFunctor)
open import Effect.Applicative using (RawApplicative)
open import Effect.Monad using (RawMonad)

open import Data.Bool
open import Data.Nat
open import Data.String


--- Playing with 'with' and inspect
import Relation.Binary.PropositionalEquality as Eq
open Eq

toℕ : Bool → ℕ
toℕ false = 0
toℕ true = 1

-- With does not recognize that the case "zero" can never occur.
toℕ-msg : Bool → String
toℕ-msg true with (toℕ true)
... | suc n = "Yes"
... | zero  = "Impossible"
toℕ-msg false = "false"

-- Bit using inspect pattern, we can show it.
toℕ-msg' : Bool → String
toℕ-msg' true with toℕ true | inspect toℕ true
... | 1 | [ k ] = {!!} --  "What is b?"
... | zero | ()
toℕ-msg' false = "false"

-------

data Foo (A : Set) : Set where
  L : A → Foo A
  R : A → Foo A

open import Function using (id; case_of_)

ggg : {A : Set} → Foo A → Foo A
ggg f@(L a) with (id f) | inspect id f
... | (L x) | [ i ] = {!!}
... | (R x) | [ i ] = {!!}
ggg f@(R a) = f

open import Data.Unit

what? : Bool → ⊤
what? true with id true | inspect id true
... | true  | [ true≡true ] = {!!}
... | false | [ false≡false ] = {!!}
what? false = tt

what2? : Bool → ⊤
what2? true with true | inspect id true
... | true | [ i ] = {!!}
... | false | [ () ]
what2? false = tt

fff : Bool → ⊤
fff true with id true
... | true = tt
... | false = tt
fff false = tt

qqq : Bool → ⊤
qqq true = case true of (λ {
    true → {!!}
  ; false → {!!}
  })
qqq false = tt

idx≡x : ∀ {A : Set} {a : A} → id a ≡ a → a ≡ a
idx≡x idx=x = refl

ff' : Bool → ⊤
ff' true = aux true (inspect id true) where
  aux : (x : Bool) → Reveal id · x is (id true) → ⊤
  aux true  [ i ] = {!!}
  aux false [ () ]
ff' false = tt
