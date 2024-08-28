```agda
{-# OPTIONS --allow-unsolved-metas #-}
```

# Proving Properties of a Language

```agda
module Vatras.Tutorial.C_Proofs where

open import Data.Product using (Σ-syntax; ∃-syntax; _,_)
open import Relation.Binary.PropositionalEquality as Eq using (_≡_; refl)

open import Vatras.Framework.Definitions
open import Vatras.Framework.VariabilityLanguage
open import Vatras.Framework.Compiler using (LanguageCompiler)

open import Vatras.Data.EqIndexedSet
```

In this tutorial, we are going to prove our language from the first
tutorial to be complete, and to be at least as expressive as
binary choice calculus `2CC`.
We will also cover what it takes to prove `soundness`, as well as
`expressiveness` in the other direction or vs. other languages.

So first, we are going to import our previous definitions and `2CC`
```agda
open import Vatras.Tutorial.A_NewLanguage
open import Vatras.Tutorial.B_Translation

open import Vatras.Lang.All
open 2CC using (2CC; 2CCL; _-<_>-; _⟨_,_⟩) renaming (⟦_⟧ to ⟦_⟧₂)
```

## Proving Expressiveness

In the last tutorial, we have shown that we can translate
binary choice calculus `2CC` to our own language `MyLang`,
and we have also proven this translation correct.
By doing this, we have shown that our own language
can express everything binary choice calculus can express
(with respect to variant maps as a semantic domain).
We can hence conclude that our language is at least
as expressive as binary choice calculus from having
constructed our compiler.
```agda
open import Vatras.Framework.Relation.Expressiveness V

MyLang≽2CC : MyVarLang ≽ 2CCL F
-- MyLang≽2CC : MyVarLang is-at-least-as-expressive-as 2CCL F
MyLang≽2CC = expressiveness-from-compiler my-compiler
```

Try to lookup the definition of `expressiveness-from-compiler` and `≽`
in your editor (`g d` in Vim or evil Emacs) to see what is going on here.
What happens is that the compiler is used to prove that for every expression
in `2CCL F`, there is an expression in `MyVarLang` with the same semantics.

_What is necessary to prove the converse property?_
```agda
2CC≽MyLang : 2CCL F ≽ MyVarLang
2CC≽MyLang = {!!}
```

Within our library, we have also constructed compilers from and to `2CC`.
Since compilation is transitive, me may compose compilers to compile our
language to other languages than `2CC`, and we can also conclude expressiveness
proofs transitively as well.

As an example let's conclude that our language must also be at least as expressive
as algebraic decision trees.
First, we are going to import
the definitions of all the variability languages defined in the library (`Lang.All`), and
the existing proofs, comparing all the languages (`Translation.LanguageMap`).
We then open an internal module from the language map which contains all the
expressiveness proofs, where we fix the annotation type `F : 𝔽` to `String`.
If you changed the definition of `F` in the first tutorial, some of the
following might not compiler.
```agda
open import Vatras.Lang.All
open import Vatras.Translation.LanguageMap
open Vatras.Translation.LanguageMap.Expressiveness-String
```

By transitivity, we can conlude that our variability language is
also at least as expressive as algebraic decision trees.
```agda
MyLang≽ADT : MyVarLang ≽ ADT.ADTL V F
MyLang≽ADT = ≽-trans MyLang≽2CC 2CC≽ADT
```

From an expressiveness proof, we can also reverse engineer the
compiler that constitutes the proof:
```agda
compile-to-ADT : LanguageCompiler (ADT.ADTL V F) MyVarLang
compile-to-ADT = compiler-from-expressiveness MyLang≽ADT
```

As an exercise, try to derive more expressiveness proofs or
compilers (as you like) for your language to (one of) the other
languages that are as expressive as `2CC` or less expressive.
Candiates to check out are `CCC`, `VariantList`, the `NCC` dialects, `OC`, and `FST.
(As can be seen in the language map and in Section 5 of our paper.)

## Proving our Language Complete

A language is complete if there is an expression for
every element in the respective semantic domain.
For variability languages as formalized in our framework,
this means that there must be an expression for every
variant map (i.e., finite, non-empty set of variants).

Properties such as completeness, soundness, and expressiveness
are parametric in the type of variants in the variant map.
We will reuse `V` here which was defined in the first tutorial
to be a rose tree just as in our paper.
(Try looking it up using your editor, and feel free to
change it if you like 🙂! (Some proofs might break but you
can just replace them by a whole to experiment a bit)).

```agda
open import Vatras.Framework.Properties.Completeness V
open import Vatras.Framework.Proof.ForFree V
open Vatras.Translation.LanguageMap.Completeness-String
```

In our library, it is already proven that binary choice calculus `2CC`
is complete. Since we have just proven above that our language is at least
as expressive as `2CC`, it must also be complete.
```agda
MyLang-is-Complete : Complete MyVarLang
MyLang-is-Complete = completeness-by-expressiveness (2CC-is-complete "🍪") MyLang≽2CC
```
Again, try to look up these definitions.
There is a whole range of interesting theorems to conclude completeness, soundness,
and expressiveness within the `Framework.Proof.Transitive` module.
The proof `2CC-is-complete` that `2CC` is complete assumes the existence of at least
one annotation (i.e., one feature name) in our annotation language `F`.
Since we fixed `F` to `String`, which means that annotations are represented by names,
any string, however it looks is fine, and so is `"🍪"` or even `""`.

Alternatively, one may prove completeness manually.
Proving it, basically requires you to write a differencing algorithm:
Given a finite, non-empty set of variants, you have to construct an expression
in your language and prove that it denotes exactly those variants:
```agda
MyLang-is-Complete' : Complete MyVarLang
MyLang-is-Complete' m =
  {!!} , -- write down the expression in this hole
  {!!}   -- write down the proof of correctness in this hole
```
We do not recommend doing this by hand because it is very tedious.
In the framework, we did it by first proving
```agda
_ : Complete (VariantList.VariantListL V)
_ = VariantList-is-Complete "🍇" V
```
and then translating `VariantList`s to the other languages,
and proving completeness via `completeness-by-expressiveness` again.
You can read more on this process in our paper.

## Proving our Language Sound

A language is sound if any of its expressions
denotes an element in the semantic domain.
For variability languages as formalized in our framework,
this means that there must be an variant map for every expression.

By inspecting the `Framework.Proof.Transitive` module closely,
you will see that proofs for soundness are exactly dual to the proofs
for completeness. For every rule on (in)completeness, there exists a proof
for (un)soundness.

All languages formalized in our `LanguageMap` are proven sound.
The soundness proofs require that we can decide equality for our annotations
which we frankly can do for strings:
```agda
open import Data.String using (_≟_)
```

Try to figure out now how to conclude soundness of your language.
```agda
open import Vatras.Framework.Properties.Soundness V

MyLang-is-Sound : Sound MyVarLang
MyLang-is-Sound = {!!}
```

## Solution for Proving Soundness

<details>
<summary>Spoiler Alert! Click me!</summary>

This is a possible proof of soundness.
```agda
MyLang-is-Sound' : Sound MyVarLang
MyLang-is-Sound' = soundness-by-expressiveness (2CC-is-sound _≟_) 2CC≽MyLang
```
It requires that we have finished the proof of `2CC≽MyLang`.
Alternatively, we could also use a soundness proof for any other existing language,
and then translate our language to it.
Soundness can also be proven directly, but this is again cumbersome, and we
only proved it directly for `VariantList` just as we did for completeness.
```agda
_ : Sound (VariantList.VariantListL V)
_ = VariantList-is-Sound V
```

</details>
