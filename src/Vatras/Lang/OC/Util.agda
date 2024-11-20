open import Vatras.Framework.Definitions using (𝔽; 𝔸; atoms)
module Vatras.Lang.OC.Util {Option : 𝔽} where

open import Size using (Size; ↑_)
open import Data.Bool using (Bool; true; false)
open import Data.List using ([]; _∷_)

open import Vatras.Util.Named
open import Vatras.Lang.OC Option using (OC; _-<_>-; Configuration)

{-|
Creates an artifact OC expression with a single child.
-}
singleton : ∀ {i : Size} {A : 𝔸} → atoms A → OC i A → OC (↑ i) A
singleton a e = a -< e ∷ [] >-

{-|
Creates a constant configuration, fixed to the given boolean value.
-}
all-oc : Bool → Configuration
all-oc b _ = b

{-|
A configuration that includes every option.
We also give the configuration a name for reuse in demo applications and tests.
-}
allyes-oc : Named Configuration
allyes-oc = all-oc true called "all-yes"

{-|
A configuration that excludes every option.
We also give the configuration a name for reuse in demo applications and tests.
-}
allno-oc : Named Configuration
allno-oc = all-oc false called "all-no " --space intended for nicer printing lol
