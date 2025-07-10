{-|
Traversable instance on non-empty lists.
part of the STL now: Data.List.NonEmpty.Effectful
-}
module Vatras.Util.NonEmptyTraversable where

open import Function using (_∘_)
open import Data.List.NonEmpty using (List⁺; _∷_)
import Data.List.Effectful
open Data.List.Effectful.TraversableA using (sequenceA)
open import Effect.Applicative using (RawApplicative)

module TraversableA⁺ {f g F} (App : RawApplicative {f} {g} F) where

  open RawApplicative App

  sequenceA⁺ : ∀ {A} → List⁺ (F A) → F (List⁺ A)
  sequenceA⁺ (x ∷ xs) = _∷_ <$> x <*> (sequenceA App xs)

  mapA⁺ : ∀ {a} {A : Set a} {B} → (A → F B) → List⁺ A → F (List⁺ B)
  mapA⁺ f = sequenceA⁺ ∘ Data.List.NonEmpty.map f

