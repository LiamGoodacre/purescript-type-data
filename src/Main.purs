module Main where

import Prelude
import Data.Maybe (Maybe)
import Type.Proxy (Proxy(..), Proxy2(..))
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)

-- boilerplate bool, nat, option, list

class IsBool ctor
data True
instance isBoolTrue
  :: IsBool True
data False
instance isBoolFalse
  :: IsBool False

class Not bool out | bool -> out
instance notT :: Not True False
instance notF :: Not False True

class And left right out | left right -> out, left out -> right, right out -> left
instance andTT :: And True True True
instance andTF :: And True False False
instance andFT :: And False True False
instance andFF :: And False False False

class If bool isTrue isFalse out | bool isTrue isFalse -> out
instance ifBoolTrue
  :: If True isTrue isFalse isTrue
instance ifBoolFalse
  :: If False isTrue isFalse isFalse

class IsNat ctor
data Zero
instance isNatZero
  :: IsNat Zero
data Succ num
instance isNatSucc
  :: IsNat num
  => IsNat (Succ num)

class EqNat l r b | l r -> b
instance eqNatZZ
  :: EqNat Zero Zero True
instance eqNatSZ
  :: EqNat (Succ l) Zero False
instance eqNatZS
  :: EqNat Zero (Succ r) False
instance eqNatSS
  :: EqNat l r bool
  => EqNat (Succ l) (Succ r) bool

data Some value
data None
class OrElse opt other out | opt other -> out
instance orElseS
  :: OrElse (Some value) other value
instance orElseN
  :: OrElse None other other

class IsList ctor
data Nil
instance isListNil
  :: IsList Nil
data Cons head tail
instance isListCons
  :: IsList tail
  => IsList (Cons head tail)

class GetLast list index last | list -> index last
instance getLastNil
  :: GetLast (Cons last Nil) Zero last
instance getLastCons
  :: GetLast (Cons head tail) index last
  => GetLast (Cons ignore (Cons head tail)) (Succ index) last


-- data structures

-- a reference to a defined type
data TypRef (moduleName :: Symbol) (typeName :: Symbol)

-- kinds
class IsKind ctor
data KindStar
instance isKindStar
  :: IsKind KindStar
data KindArr domain codomain
instance isKindArr
  :: (IsKind domain, IsKind codomain)
  => IsKind (KindArr domain codomain)
data KindConstraint
instance isKindConstraint
  :: IsKind KindConstraint
data KindSymbol
instance isKindSymbol
  :: IsKind KindSymbol

-- data constructors
data Ctor (ctorName :: Symbol) ctorArgs

-- data types
data DataType typRef typParams ctors

-- variance of a type variable
data Variance pos neg
type Bivariant = Variance True True
type Covariant = Variance True False
type Contravariant = Variance False True
type Invariant = Variance False False

class NegateVariance variance out | variance -> out
instance negateVariance
  :: (Not pos notPos,
      Not neg notNeg)
  => NegateVariance (Variance pos neg) (Variance notPos notNeg)

class AndVariance left right out | left right -> out
instance andVariance
  :: (And lPos rPos oPos,
      And lNeg rNeg oNeg)
  => AndVariance (Variance lPos lNeg) (Variance rPos rNeg) (Variance oPos oNeg)

class NegateOptionVariance variance out | variance -> out
instance negateOptionVarianceS
  :: NegateVariance variance notVariance
  => NegateOptionVariance (Some variance) (Some notVariance)
instance negateOptionVarianceN
  :: NegateOptionVariance None None

class UnifyOptionVariance left right out | left right -> out
instance unifyVarianceSS
  :: AndVariance left right out
  => UnifyOptionVariance (Some left) (Some right) (Some out)
instance unifyVarianceSN
  :: UnifyOptionVariance (Some left) None (Some left)
instance unifyVarianceNS
  :: UnifyOptionVariance None (Some right) (Some right)
instance unifyVarianceNN
  :: UnifyOptionVariance None None None



class IsTypExpr ctor
data TypVar index
instance isTypExprVar
  :: IsNat index
  => IsTypExpr (TypVar index)
data TypForall body
instance isTypExprForall
  :: IsTypExpr body
  => IsTypExpr (TypForall body)
data TypArr domain codomain
instance isTypExprArr
  :: (IsTypExpr domain,
      IsTypExpr codomain)
  => IsTypExpr (TypArr domain codomain)

type V0 = TypVar Zero
type V1 = TypVar (Succ Zero)


class IsDataType  (typ :: *)      dataTyp | typ -> dataTyp, dataTyp -> typ
class IsDataType1 (typ :: * -> *) dataTyp | typ -> dataTyp, dataTyp -> typ


class VarianceInTypeExpr varRef expr varianceOpt | varRef expr -> varianceOpt
instance varianceInTypeExprVar
  :: (EqNat varRef typVar eq,
      If eq (Some (Variance True False)) None varianceOpt)
  => VarianceInTypeExpr varRef (TypVar typVar) varianceOpt
instance varianceInTypeExprForall
  :: VarianceInTypeExpr (Succ varRef) body varianceOpt
  => VarianceInTypeExpr varRef (TypForall body) varianceOpt
instance varianceInTypeExprArr
  :: (VarianceInTypeExpr varRef domain domainVarianceOpt,
      VarianceInTypeExpr varRef codomain codomainVarianceOpt,
      NegateOptionVariance domainVarianceOpt notDomainVarianceOpt,
      UnifyOptionVariance notDomainVarianceOpt codomainVarianceOpt varianceOpt)
  => VarianceInTypeExpr varRef (TypArr domain codomain) varianceOpt

class VarianceInType varRef expr variance | varRef expr -> variance
instance varianceInType
  :: (VarianceInTypeExpr varRef expr varianceOpt,
      OrElse varianceOpt (Variance True True) variance)
  => VarianceInType varRef expr variance

class VarianceInCtorArgs varRef list varianceOpt | varRef list -> varianceOpt
instance varianceInCtorNil
  :: VarianceInCtorArgs varRef Nil None
instance varianceInCtorCons
  :: (VarianceInTypeExpr varRef head headVariance,
      VarianceInCtorArgs varRef tail tailVariance,
      UnifyOptionVariance headVariance tailVariance varianceOpt)
  => VarianceInCtorArgs varRef (Cons head tail) varianceOpt

class VarianceInCtor varRef ctor varianceOpt | varRef ctor -> varianceOpt
instance varianceInCtor
  :: VarianceInCtorArgs varRef args varianceOpt
  => VarianceInCtor varRef (Ctor name args) varianceOpt

class VarianceInDataTypeCtors varRef list varianceOpt | varRef list -> varianceOpt
instance varianceInDataTypeNil
  :: VarianceInDataTypeCtors varRef Nil None
instance varianceInDataTypeCons
  :: (VarianceInCtor varRef head headVariance,
      VarianceInDataTypeCtors varRef tail tailVariance,
      UnifyOptionVariance headVariance tailVariance varianceOpt)
  => VarianceInDataTypeCtors varRef (Cons head tail) varianceOpt

class VarianceInDataType varRef dataType varianceOpt | varRef dataType -> varianceOpt
instance varianceInDataType
  :: VarianceInDataTypeCtors varRef ctors varianceOpt
  => VarianceInDataType varRef (DataType typRef params ctors) varianceOpt

class IsFunctor dataType outcome | dataType -> outcome
instance isFunctor
  :: (GetLast args varRef varKind,
      VarianceInDataTypeCtors varRef ctors varianceOpt,
      OrElse varianceOpt (Variance True True) (Variance pos neg),
      -- must not appear in contravariant position
      Not neg outcome)
  => IsFunctor (DataType typRef args ctors) outcome

checkFunctor
  :: forall typ dataType outcome
  . (IsDataType1 typ dataType,
     IsFunctor dataType outcome)
  => Proxy2 typ -> Proxy outcome
checkFunctor _ = Proxy

checkVariance :: forall varRef typExpr var. (VarianceInType varRef typExpr var) =>
  Proxy typExpr -> Proxy varRef -> Proxy var
checkVariance _ _ = Proxy

exampleBivariant :: Proxy (Variance True True)
exampleBivariant = checkVariance
  (Proxy :: Proxy (TypArr (TypVar (Succ Zero)) (TypVar (Succ Zero))))
  (Proxy :: Proxy Zero)

exampleInvariant :: Proxy (Variance False False)
exampleInvariant = checkVariance
  (Proxy :: Proxy (TypArr (TypVar Zero) (TypVar Zero)))
  (Proxy :: Proxy Zero)

exampleCovariant :: Proxy (Variance True False)
exampleCovariant = checkVariance
  (Proxy :: Proxy (TypArr (TypVar (Succ Zero)) (TypVar Zero)))
  (Proxy :: Proxy Zero)

exampleContravariant :: Proxy (Variance False True)
exampleContravariant = checkVariance
  (Proxy :: Proxy (TypArr (TypVar Zero) (TypVar (Succ Zero))))
  (Proxy :: Proxy Zero)



-- instance of IsDataType for Maybe
instance maybeDataType
  :: IsDataType1 Maybe
     (DataType (TypRef "Data.Maybe" "Maybe") (Cons KindStar Nil)
      (Cons (Ctor "Nothing" Nil)
       (Cons (Ctor "Just" (Cons (TypVar Zero) Nil))
        Nil)))

-- will infer `True`
exampleIsFunctor :: Proxy _
exampleIsFunctor = checkFunctor (Proxy2 :: Proxy2 Maybe)



main :: forall e. Eff (console :: CONSOLE | e) Unit
main = do
  log "Hello datatypes!"

