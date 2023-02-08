module Show.Lines where

open import Data.Nat using (ℕ)
open import Data.List using (List; map; concat)
open import Data.String using (String; _++_; replicate)
open import Function using (id)

open import Effect.Applicative using (RawApplicative)
open RawApplicative using (pure)
open import Data.List.Effectful renaming (applicative to list-applicative)
open import Level using (0ℓ)

-- Line monad.
-- It captures a sequence of text lines which we aim to print.
-- Under the hood it is just a list of strings but with slightly different behaviour (see _>>_ below).
Lines : Set
Lines = List String

-- print a single line
line : String → Lines
line = pure list-applicative

-- syntactic sugar to create lines by preceeding expressions of type String with >
>_ : String → Lines
>_ = line
infix 1 >_

-- add a sequence of lines to the output at once
lines : List Lines → Lines
lines = concat

-- Export the composition operator do allow do-notation.
-- We do not rely on _>>_ of the list monad because it forgets the first argument and just keeps the second list. We thus would forget everything we wanted to print except for the last line.
_>>_ : Lines → Lines → Lines
_>>_ = Data.List._++_

-- Some smart constructors

-- add a prefix to every line
prefix : String → Lines → Lines
prefix s lines = map (_++_ s) lines

-- indent all lines by the given number of spaces
indent : ℕ → Lines → Lines
indent i = prefix (replicate i ' ')

-- write a big headline consisting of a tag and a title
headline : String → String → Lines
headline tag title = > "================[ " ++ tag ++ " ] " ++ title ++ " ================"

linebreak : Lines
linebreak = > ""
