module Framework.Annotation.Name where

open import Data.Bool using (Bool)
open import Data.String using (String)
import Data.String.Properties

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

-- Names are just strings. We could also pick natural numbers depending on what's easier for the proofs. With strings it is easier though to avoid name clashs.
Name : Set
Name = String

_≟_ : Decidable (_≡_)
_≟_ = Data.String.Properties._≟_

_==_ : Name → Name → Bool
_==_ = Data.String.Properties._==_

-- Some common names for names.

-- Names are referred to as "Dimensions" in choice calculus.
Dimension : Set
Dimension = Name

-- In option calculus, names identify options.
Option : Set
Option = Name

-- In algebraic decision diagrams, names are usually referred to as "Variables".
Variable : Set
Variable = Name

