module Show.Lines where

open import Data.Bool using (true; false; if_then_else_)
open import Data.Nat using (ℕ; _*_; _∸_; ⌊_/2⌋; ⌈_/2⌉; _≤ᵇ_)
open import Data.List as List using (List; _∷_; [_]; concat; splitAt; _∷ʳ_)
open import Data.Maybe using (nothing; just)
open import Data.String using (String; _++_; _==_; replicate; fromChar; toList; fromList; Alignment; fromAlignment)
open import Data.Product as Prod using (_,_; proj₁; map₁)
open import Data.Unit using (⊤; tt)
open import Function using (id; _∘_)

open import Algebra using (RawMonoid)
open import Effect.Applicative using (RawApplicative)
open import Effect.Functor using (RawFunctor)
open import Effect.Monad using (RawMonad)
open import Effect.Monad.Writer as Writer using (RawMonadWriter; Writer; runWriter)
open import Data.List.Effectful as List using () renaming (applicative to list-applicative; monad to list-monad)
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
Lines' : Set → Set
Lines' = Writer (List.++-[]-rawMonoid Line)

Lines : Set
Lines = Lines' (Level.Lift Level.zero ⊤)

-- Export the composition operator to allow do-notation.
open Writer using (functor; applicative; monad) public
open RawMonad {f = 0ℓ} (monad {𝕎 = List.++-[]-rawMonoid Line}) using (_>>_; _>>=_) public

noLines : Lines
noLines = pure (Level.lift tt)
  where
  open RawApplicative applicative

-- print a single line
single : Line → Lines
single line = tell [ line ]
  where
  open RawMonadWriter Writer.monadWriter

-- add a sequence of lines to the output at once
lines : List Lines → Lines
lines lines = sequenceA lines >> noLines
  where
  open List.TraversableA applicative

map-lines : {A : Set} → (List Line → List Line) → Lines' A → Lines' A
map-lines f = writer ∘ map₁ f ∘ runWriter
  where
  open RawMonadWriter Writer.monadWriter

map : {A : Set} → (Line → Line) → Lines' A → Lines' A
map f = map-lines (List.map f)

raw-lines : Lines → List Line
raw-lines = proj₁ ∘ runWriter

for-loop : ∀ {ℓ} {A : Set ℓ} → List A → (A → Lines) → Lines
for-loop items op = lines (List.map op items)

syntax for-loop items (λ c → l) = foreach [ c ∈ items ] l

align-all : ℕ → Lines → Lines
align-all width = map (align width)

overwrite-alignment-with : Alignment → Lines → Lines
overwrite-alignment-with a = map (λ l → record l { alignment = a })

-- Some smart constructors

[_]>_ : Alignment → String → Lines
[ a ]> l = single (record { alignment = a; content = l })
infix 1 [_]>_

>_ : String → Lines
>_ = [ Left ]>_
infix 1 >_

>∷_ : List String → Lines
>∷_ = lines ∘ List.map >_
infix 1 >∷_

phantom : String → String
phantom s = replicate (Data.String.length s) ' '

mantle : String → String → Lines → Lines
mantle prefix suffix = map (manipulate (λ s → prefix ++ s ++ suffix))

prefix : String → Lines → Lines
prefix p = mantle p ""

suffix : String → Lines → Lines
suffix s = mantle "" s

modifyLastLine : (Line → Line) -> Lines → Lines
modifyLastLine f ls with List.unsnoc (raw-lines ls)
modifyLastLine f ls | nothing = noLines
modifyLastLine f ls | just (init , last) = tell (init ∷ʳ f last)
  where
  open RawMonadWriter Writer.monadWriter

appendToLastLine : String → Lines → Lines
appendToLastLine suffix = modifyLastLine λ where
  (alignment aligned line) → alignment aligned (line ++ suffix)

-- indent all lines by the given number of spaces
indent : ℕ → Lines → Lines
indent i = prefix (replicate i ' ')

linebreak : Lines
linebreak = > ""

width : Lines → ℕ
width = max ∘ List.map length ∘ raw-lines

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
wrap-all-at max-width ls = lines (List.map (wrap-at max-width) (raw-lines ls))

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
