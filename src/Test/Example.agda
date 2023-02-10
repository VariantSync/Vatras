module Test.Example where

open import Data.String using (String)
open import Util.Named public

Example = Named

pattern _example:_ name e = e called name
infix 2 _example:_
