module Show.Lines where

open import Data.Bool using (true; false; if_then_else_)
open import Data.Nat using (ℕ; _*_; _∸_; ⌊_/2⌋; ⌈_/2⌉; _≤ᵇ_)
open import Data.List using (List; _∷_; map; concat; splitAt)
open import Data.String using (String; _++_; _==_; replicate; fromChar; toList; fromList; Alignment; fromAlignment)
open import Data.Product as Prod using (_,_)
open import Function using (id; _∘_)

open import Effect.Applicative using (RawApplicative)
open import Effect.Monad using (RawMonad)
open RawApplicative using (pure)
open import Data.List.Effectful renaming (applicative to list-applicative; monad to list-monad)
open import Level using (0ℓ)

open import Util.List using (max)

open Data.String using (Left; Center; Right) public

record Line : Set where
  constructor _aligned_
  field
    alignment : Alignment
    content : String
open Line public

manipulate : (String → String) → Line → Line
manipulate f l = record l { content = f (content l) }

align : ℕ → Line → Line
align width line = manipulate (fromAlignment (alignment line) width) line

length : Line → ℕ
length line = Data.String.length (content line)

-- Lines monad.
-- It captures a sequence of text lines which we aim to print.
-- Under the hood it is just a list of strings but with slightly different behaviour (see _>>_ below).
Lines : Set
Lines = List Line

-- print a single line
single : Line → Lines
single = pure list-applicative

-- add a sequence of lines to the output at once
lines : List Lines → Lines
lines = concat

align-all : ℕ → Lines → Lines
align-all width = map (align width)

overwrite-alignment-with : Alignment → Lines → Lines
overwrite-alignment-with a = map (λ l → record l { alignment = a })

-- Export the composition operator do allow do-notation.
-- We do not rely on _>>_ of the list monad because it forgets the first argument and just keeps the second list. We thus would forget everything we wanted to print except for the last line.
_>>_ : Lines → Lines → Lines
_>>_ = Data.List._++_

-- Some smart constructors

[_]>_ : Alignment → String → Lines
[ a ]> l = single (record { alignment = a; content = l })
infix 1 [_]>_

>_ : String → Lines
>_ = [_]>_ Left
infix 1 >_

>∷_ : List String → Lines
>∷_ = lines ∘ map >_
infix 1 >∷_

mantle : String → String → Lines → Lines
mantle prefix suffix = map (manipulate (λ s → prefix ++ s ++ suffix))

prefix : String → Lines → Lines
prefix p = mantle p ""

suffix : String → Lines → Lines
suffix s = mantle "" s

-- indent all lines by the given number of spaces
indent : ℕ → Lines → Lines
indent i = prefix (replicate i ' ')

linebreak : Lines
linebreak = > ""

width : Lines → ℕ
width = max ∘ map length

-- Given a maximum length, this function wraps a given line as often as necessary to not exceed that width,
-- This is not guaranteed to terminate because the list could be infinite.
{-# NON_TERMINATING #-}
wrap-at : ℕ → Line → Lines
wrap-at max-width line with (length line) ≤ᵇ max-width
... | true  = single line
... | false = let first-line , rest = splitAt max-width (toList (content line))
               in do
                  > fromList first-line
                  wrap-at max-width ((alignment line) aligned fromList rest)

-- Wraps all lines at the given maximum width using wrap-at.
wrap-all-at : ℕ → Lines → Lines
wrap-all-at max-width lines =
  let open RawMonad list-monad in
  lines >>= wrap-at max-width

-- Dr
boxed : ℕ → (title : String) → (content : Lines) → Lines
boxed width title content =
  let h  = '─'
      v  = '│'
      tl = '╭'
      bl = '╰'
      tr = '╮'
      br = '╯'

      total-titlebar-len = width ∸ (Data.String.length title) ∸ 4 -- 2x whitespace + 2x corners
      left-titlebar-len  = ⌊ total-titlebar-len /2⌋
      right-titlebar-len = ⌈ total-titlebar-len /2⌉

      content-indent-width = 2
      content-indent = replicate content-indent-width ' '
      content-width  = width ∸ (2 * content-indent-width) ∸ 2 -- left and right bound

      title-spacing = fromChar (if (title == "") then h else ' ')
      header = (replicate left-titlebar-len h) ++ title-spacing ++ title ++ title-spacing ++ (replicate right-titlebar-len h)
      footer = replicate (Data.String.length header) h
  in do
    -- print the header of the box
    > (fromChar tl) ++ header ++ (fromChar tr)
    -- print the content
    -- wrap the content such that it fits in the box
    -- then pad it according to our alignment so that all lines have length of the box
    -- then draw box lines on the left and right
    mantle (fromChar v ++ content-indent)
           (content-indent ++ fromChar v)
           (align-all content-width
             (wrap-all-at content-width content)
           )
    -- print the footer of the box
    > (fromChar bl) ++ footer ++ (fromChar br)
