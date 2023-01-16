module Lang.Annotation.Dimension where

open import Data.Bool using (Bool)
open import Data.String using (String)
import Data.String.Properties

open import Relation.Binary.Definitions using (Decidable)
open import Relation.Binary.PropositionalEquality using (_≡_)

Dimension : Set
Dimension = String

_≟_ : Decidable (_≡_)
_≟_ = Data.String.Properties._≟_

_==_ : Dimension → Dimension → Bool
_==_ = Data.String.Properties._==_

