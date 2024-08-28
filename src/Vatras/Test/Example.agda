module Vatras.Test.Example where

open import Data.String using (String)
open import Vatras.Util.Named public

Example = Named

pattern _≔_ name e = e called name
infix 2 _≔_
