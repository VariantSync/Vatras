module Vatras.SyntacticExpressiveness.Reflection where

open import Data.Product using (_×_; _,_; Σ-syntax; map₁; uncurry; proj₁; proj₂; map₂)
open import Data.Sum using (_⊎_)
open import Data.Nat as ℕ hiding (_≡ᵇ_)
import Data.Nat.Properties as ℕ
open import Level renaming (zero to lzero; suc to lsuc)
open import Data.Bool
open import Data.Unit
open import Data.Maybe as Maybe using (maybe; is-just)
open import Data.List
open import Data.List.NonEmpty as List⁺ using (List⁺; _∷_)
import Data.List.Effectful
import Data.Nat.Show as ℕ
open import Data.String as S using (String)
import Effect.Monad.Identity
open import Function
open import Relation.Binary.PropositionalEquality
open import Size
open import Reflection
open import Reflection.AST
open import Reflection.AST.Argument as Argument hiding (map)
open import Reflection.AST.Argument.Information
open import Reflection.AST.Argument.Visibility
open import Reflection.AST.Name
open import Reflection.AST.Term
open import Reflection.AST.Pattern
open import Reflection.AST.Show
import Reflection.AST.Traversal
open import Reflection.TCM.Syntax
import Reflection.TCM.Effectful as TCM
open Data.List.Effectful.TraversableM (TCM.monad {lzero})

open import Vatras.Framework.Definitions

module SizeByReflection where
  private
    infixr 1 _=<<_
    _=<<_ : ∀ {a} {b} {A : Set a} {B : Set b} → (B → TC A) → TC B → TC A
    _=<<_ = flip bindTC

  hide : ∀ {a} {A : Set a} → Arg A → Arg A
  hide (arg (arg-info _ m) a) = arg (arg-info hidden m) a

  getDataDefinition : Name → TC (ℕ × List Name)
  getDataDefinition n = go =<< getDefinition n
    where
    go : Definition → TC (ℕ × List Name)
    go (data-type arity constructors) = pure (arity , constructors)
    go _ = typeError (strErr "The given name \"" ∷ nameErr n ∷ strErr "\" must be a data type" ∷ [])

  deconstructFunctionType : Type → List (String × Arg Type) × Type
  deconstructFunctionType (pi argType (abs n resultType)) = map₁ ((n , argType) ∷_) (deconstructFunctionType resultType)
  deconstructFunctionType rest = [] , rest

  getArgs : Name → TC (List (String × Arg Type) × Type)
  getArgs functionName = deconstructFunctionType <$> getType functionName

  mapWithIndex : ∀ {a b} {A : Set a} {B : Set b} → (ℕ → A → B) → List A → List B
  mapWithIndex {A = A} {B = B} f xs = go (length xs) xs
    where
    go : ℕ → List A → List B
    go zero xs = []
    go (suc i) [] = []
    go (suc i) (x ∷ xs) = f i x ∷ go i xs

  withIndex : ∀ {a} {A : Set a} → List A → List (ℕ × A)
  withIndex = mapWithIndex (_,_)

  withIndexReverse : ∀ {a} {A : Set a} → List A → List (ℕ × A)
  withIndexReverse xs = zip (upTo (length xs)) xs

  mapWithIndexReverse : ∀ {a b} {A : Set a} {B : Set b} → (ℕ → A → B) → List A → List B
  mapWithIndexReverse f xs = zipWith f (upTo (length xs)) xs

  removeIndices : ∀ {a} {A : Set a} → List ℕ → List A → List A
  removeIndices {A = A} is = go zero
    where
    go : ℕ → List A → List A
    go i [] = []
    go i (x ∷ xs) = if is-just (findᵇ (ℕ._≡ᵇ_ i) is) then go (suc i) xs else x ∷ go (suc i) xs

  module _ where
    open Effect.Monad.Identity
    open Reflection.AST.Traversal applicative

    fixVarsTerm : (ℕ → ℕ) → Term → Term
    fixVarsTerm f = runIdentity ∘ traverseTerm (record defaultActions { onVar = λ _ i → mkIdentity (f i) }) (0 , [])

    fixVarsArgTerm : (ℕ → ℕ) → Arg Term → Arg Term
    fixVarsArgTerm f (arg info term) = arg info (runIdentity (traverseTerm (record defaultActions { onVar = λ _ i → mkIdentity (f i) }) (0 , []) term))

    fixVarsPats : (ℕ → ℕ) → List (Arg Pattern) → List (Arg Pattern)
    fixVarsPats f = runIdentity ∘ traversePats (record defaultActions { onVar = λ _ i → mkIdentity (f i) }) (0 , [])

  handleRecursiveArgs : Name → (List (Arg Term) → Term) → List (ℕ × ℕ) → List (ℕ × Arg Term) → TC (List Term)
  handleRecursiveArgs n sizeFun sizeFuns [] = pure []
  handleRecursiveArgs n sizeFun sizeFuns ((i , arg _ (def n' args)) ∷ as) with n ≡ᵇ n'
  -- handle recursion
  handleRecursiveArgs n sizeFun sizeFuns ((i , arg _ (def n' args)) ∷ as) | true = do
    is <- handleRecursiveArgs n sizeFun sizeFuns as
    pure (sizeFun (var i [] ⟨∷⟩ []) ∷ is)
  -- handle atoms
  handleRecursiveArgs n sizeFun sizeFuns ((i , arg _ (def (quote atoms) (arg _ (var Ai []) ∷ []))) ∷ as) | false = do
    is <- handleRecursiveArgs n sizeFun sizeFuns as
    pure (def (quote atomSize) (var (suc Ai + length as) [] ⟨∷⟩ var i [] ⟨∷⟩ []) ∷ is)
  -- special case List(⁺) (for now)
  handleRecursiveArgs n sizeFun sizeFuns ((i , arg _ (def n' (_ ∷ arg _ (def n'' _) ∷ []))) ∷ as) | false = do
    is <- handleRecursiveArgs n sizeFun sizeFuns as
    if quote List ≡ᵇ n' ∧ n ≡ᵇ n''
      then pure (def (quote sum) (def (quote map) (sizeFun [] ⟨∷⟩ var i [] ⟨∷⟩ []) ⟨∷⟩ []) ∷ is)
      else if quote List⁺ ≡ᵇ n' ∧ n ≡ᵇ n''
        then pure (def (quote sum) (def (quote map) (sizeFun [] ⟨∷⟩ def (quote List⁺.toList) (var i [] ⟨∷⟩ []) ⟨∷⟩ []) ⟨∷⟩ []) ∷ is)
        else pure is
  handleRecursiveArgs n sizeFun sizeFuns ((i , arg _ (def n' args)) ∷ as) | false = handleRecursiveArgs n sizeFun sizeFuns as
  -- handle size functions
  handleRecursiveArgs n sizeFun sizeFuns ((i , arg _ (var j args)) ∷ as) = do
    is <- handleRecursiveArgs n sizeFun sizeFuns as
    maybe
      (λ (_ , i') → pure (var i' (var i [] ⟨∷⟩ []) ∷ is))
      (pure is)
      (findᵇ (λ (j' , _) → j' ℕ.≡ᵇ j + i) sizeFuns)
  handleRecursiveArgs n sizeFun sizeFuns ((i , arg _ _) ∷ as) = handleRecursiveArgs n sizeFun sizeFuns as

  typeArguments : Type → TC (List (Arg Term))
  typeArguments (def f args) = pure args
  typeArguments term = typeError (strErr "typeArguments got " ∷ termErr term ∷ [])

  appendArguments : Term → List (Arg Term) → TC Term
  appendArguments (var i args) args' = pure (var i (args ++ args'))
  appendArguments (con c args) args' = pure (con c (args ++ args'))
  appendArguments (def f args) args' = pure (def f (args ++ args'))
  appendArguments term args' = typeError (strErr "Cannot add arguments to " ∷ termErr term ∷ [])

  sizeFunType : String → Type → Term → TC Type
  sizeFunType n type shape = do
    args , _ <- deconstructFunctionType <$> normalise type -- TODO type can contain free variables
    type <- appendArguments (fixVarsTerm (_+ length args) shape) (mapWithIndex (λ where i (n , arg info _) → arg info (var i [])) args)
    pure (foldr
      (λ (n , a) t → pi (hide a) (abs n t))
      (pi
        (vArg type)
        (abs n (def (quote ℕ) [])))
      args)

  sizeType : Name → List ℕ → TC Type
  sizeType n unsizedArgs = do
    args , _ <- getArgs n

    let langType = vArg (def n (mapWithIndex (λ where i (_ , arg info _) → arg info (var (i + length args ∸ length unsizedArgs) [])) args))
    let expr→ℕ = pi langType (abs "expr" (def (quote ℕ) []))

    sizeFuns→expr→ℕ <- foldr
      (λ where (i , (n , arg info a)) t' → do
        t <- t'
        sizeFun <- sizeFunType n a (var i [])
        pure (pi (vArg sizeFun) (abs (n S.++ "-size") t)))
      (pure expr→ℕ)
      (removeIndices unsizedArgs (withIndex args))

    pure (foldr
      (λ (n , a) t → pi (hide a) (abs n t))
      sizeFuns→expr→ℕ
      args)

  sizeClause : Name → Name → ℕ → List ℕ → Name → TC Clause
  sizeClause typeName sizeFunctionName arity unsizedArgs c = do
    -- type arguments
    targs , _ <- getArgs typeName

    -- constructor arguments
    cargs , cResultType <- getArgs c
    cResultArgs <- typeArguments cResultType

    let numSizeFuns = length targs ∸ length unsizedArgs
    sizeFunTypes <- mapM
      (λ where (funTypeI , (argName , arg _ argType) , arg _ argShape) → do
        funType <- sizeFunType argName argType argShape
        pure (argName S.++ "-size" , vArg funType))
      (withIndexReverse (removeIndices unsizedArgs (zip targs cResultArgs)))

    let argsPats = applyUpTo (λ argI → hArg (var (length cargs ∸ suc argI + numSizeFuns))) arity
    let indiciesPats = fixVarsPats (_+ numSizeFuns) (map (λ where (arg _ a) → hArg (dot a)) (drop arity cResultArgs))
    let sizeFunPats = applyDownFrom (λ sizeFunI → vArg (var sizeFunI)) numSizeFuns
    let cargsPats = con c (mapWithIndex (λ where cargI (_ , arg info _) → arg info (var (cargI + numSizeFuns))) (drop arity cargs)) ⟨∷⟩ []

    sizeOperands <- sequenceM (mapWithIndex
      (λ where
          funI (arg _ (var typeI [])) → pure (typeI , funI)
          funI (arg _ term) → typeError (strErr "Cannot yet apply size functions to specialized indicies" ∷ []))
      (removeIndices unsizedArgs cResultArgs))
    recursiveSize <- handleRecursiveArgs
      typeName
      (λ args → def sizeFunctionName (applyDownFrom (λ i → vArg (var i [])) numSizeFuns ++ args))
      sizeOperands
      (mapWithIndex (λ where argI (_ , argType) → argI + numSizeFuns , argType) cargs)

    pure (clause
      (cargs
        ++ sizeFunTypes)
      (argsPats
        ++ indiciesPats
        ++ sizeFunPats
        ++ cargsPats)
      (con (quote suc)
        (foldl (λ acc t →
          def (quote _+_) (vArg acc ∷ vArg t ∷ []))
          (quoteTerm zero)
          recursiveSize
        ⟨∷⟩ [])))

  generateSize : Name → Name → List ℕ → TC ⊤
  generateSize lang fun unsizedArgs = do
    declareDef (vArg fun) =<< sizeType lang unsizedArgs
    arity , constructors <- getDataDefinition lang
    defineFun fun =<< mapM (sizeClause lang fun arity unsizedArgs) constructors

import Vatras.Framework.Variants as V
open import Vatras.Lang.All

unquoteDecl CCC-size = SizeByReflection.generateSize (quote CCC.CCC) CCC-size (0 ∷ 1 ∷ 2 ∷ [])
unquoteDecl 2CC-size = SizeByReflection.generateSize (quote 2CC.2CC) 2CC-size (0 ∷ 1 ∷ 2 ∷ [])
unquoteDecl OC-size = SizeByReflection.generateSize (quote OC.OC) OC-size (0 ∷ 1 ∷ 2 ∷ [])
unquoteDecl ADT-size = SizeByReflection.generateSize (quote ADT.ADT) ADT-size (0 ∷ 2 ∷ [])

_ : CCC-size {String} {_} {NAT} ((0 , 0) CCC.-< (1 , 1) CCC.-< [] >- ∷ "A" CCC.⟨ (2 , 2) CCC.-< [] >- ∷ (3 , 3) CCC.-< (4 , 4) CCC.-< [] >- ∷ [] >- ∷ [] ⟩ ∷ [] >-) ≡ 16
_ = refl

_ : 2CC-size {String} {_} {NAT} ((0 , 0) 2CC.-< (1 , 1) 2CC.-< [] >- ∷ "A" 2CC.⟨ (2 , 2) 2CC.-< [] >- , (3 , 3) 2CC.-< (4 , 4) 2CC.-< [] >- ∷ [] >- ⟩ ∷ [] >-) ≡ 16
_ = refl

_ : OC-size {String} {_} {NAT} ((0 , 0) OC.-< (1 , 1) OC.-< [] >- ∷ "A" OC.❲ (3 , 3) OC.-< "B" OC.❲ (4 , 4) OC.-< [] >- ❳ ∷ [] >- ❳ ∷ [] >-) ≡ 14
_ = refl

sizeRose : ∀ {i : Size} {A : 𝔸} → V.Rose i A → ℕ
sizeRose {A = A} (a V.-< cs >-) = suc (atomSize A a + sum (map sizeRose cs))

_ : ADT-size {String} {V.Rose ∞} {NAT} sizeRose ("A" ADT.⟨ ADT.leaf ((1 , 1) V.-< [] >-) , "B" ADT.⟨ ADT.leaf ((2 , 2) V.-< [] >-) , ADT.leaf ((3 , 3) V.-< (4 , 4) V.-< [] >- ∷ [] >-) ⟩ ⟩) ≡ 19
_ = refl
