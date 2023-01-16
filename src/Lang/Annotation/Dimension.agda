module Lang.Annotation.Dimension where

open import Data.String using (String)

import Data.String.Properties
open import Relation.Binary.Definitions using (Decidable)


Dimension : Set
Dimension = String

_≟_ : Decidable (_≡_)
_≟_ = Data.String.Properties._≟_

_==_ : Dimension → Dimension → Bool
_==_ = Data.String.Properties._==_
