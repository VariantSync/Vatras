module Framework.V2.Annotation.Name where

{-|
Names are used to identify elements.
Names may stem from a set of symbols, each symbol constituting a (unique) name.
We abstract such a set of symbols simply by a type whose instances can be the symbols.
For instance, Name String uses strings as names while Name ℕ uses natural numbers.
-}
Name : ∀ {ℓ} → Set ℓ → Set ℓ
Name N = N

-- other names for names ;)
Dimension = Name
Variable = Name
