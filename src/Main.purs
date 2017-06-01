module Main where

import Prelude
import Data.Maybe (Maybe)
import Type.Proxy (Proxy(..), Proxy2(..))
import Type.Data.Boolean (kind Boolean, True, False, class Not, class And, BProxy(..))
import Control.Monad.Eff (Eff)
import Control.Monad.Eff.Console (CONSOLE, log)

-- boilerplate bool, nat, option, list

class If (bool :: Boolean)
         (isTrue :: Type)
         (isFalse :: Type)
         (out :: Type)
         | bool isTrue isFalse -> out

instance ifBoolTrue
  :: If True isTrue isFalse isTrue

instance ifBoolFalse
  :: If False isTrue isFalse isFalse


foreign import data Zero :: Type

foreign import data Succ :: Type -- pred
                         -> Type


class EqNat (left :: Type)
            (right :: Type)
            (out :: Boolean)
            | left right -> out

instance eqNatZZ
  :: EqNat Zero Zero True

instance eqNatSZ
  :: EqNat (Succ l) Zero False

instance eqNatZS
  :: EqNat Zero (Succ r) False

instance eqNatSS
  :: EqNat l r bool
  => EqNat (Succ l) (Succ r) bool


foreign import data None :: Type

foreign import data Some :: Type -- value
                         -> Type


class OrElse (opt :: Type)
             (other :: Type)
             (out :: Type)
             | opt other -> out

instance orElseS
  :: OrElse (Some value) other value

instance orElseN
  :: OrElse None other other


foreign import data Nil :: Type

foreign import data Cons :: Type -- head
                         -> Type -- tail
                         -> Type


class GetLast (list :: Type)
              (index :: Type)
              (last :: Type)
              | list -> index last

instance getLastNil
  :: GetLast (Cons last Nil) Zero last

instance getLastCons
  :: GetLast (Cons head tail) index last
  => GetLast (Cons ignore (Cons head tail)) (Succ index) last


-- data structures

-- a reference to a defined type
foreign import data DataRef :: Symbol -- moduleName
                            -> Symbol -- typeName
                            -> Type


-- kinds

foreign import data KindType :: Type

foreign import data KindArr :: Type -- domain
                            -> Type -- codomain
                            -> Type

foreign import data KindConstraint :: Type

foreign import data KindSymbol :: Type


-- data constructors
foreign import data Ctor :: Symbol -- ctorName
                         -> Type   -- ctorArgs
                         -> Type

-- data types
foreign import data DataType :: Type -- typRef
                             -> Type -- typParams
                             -> Type -- ctors
                             -> Type


-- variance of a type variable

foreign import data Variance :: Boolean -- positive
                             -> Boolean -- negative
                             -> Type


class NegateVariance (variance :: Type)
                     (out :: Type)
                     | variance -> out

instance negateVariance
  :: (Not pos notPos,
      Not neg notNeg)
  => NegateVariance (Variance pos neg) (Variance notPos notNeg)


class AndVariance (left :: Type)
                  (right :: Type)
                  (out :: Type)
                  | left right -> out

instance andVariance
  :: (And lPos rPos oPos,
      And lNeg rNeg oNeg)
  => AndVariance (Variance lPos lNeg) (Variance rPos rNeg) (Variance oPos oNeg)


class NegateOptionVariance (variance :: Type)
                           (out :: Type)
                           | variance -> out

instance negateOptionVarianceS
  :: NegateVariance variance notVariance
  => NegateOptionVariance (Some variance) (Some notVariance)

instance negateOptionVarianceN
  :: NegateOptionVariance None None


class UnifyOptionVariance (left :: Type)
                          (right :: Type)
                          (out :: Type)
                          | left right -> out

instance unifyVarianceSS
  :: AndVariance left right out
  => UnifyOptionVariance (Some left) (Some right) (Some out)

instance unifyVarianceSN
  :: UnifyOptionVariance (Some left) None (Some left)

instance unifyVarianceNS
  :: UnifyOptionVariance None (Some right) (Some right)

instance unifyVarianceNN
  :: UnifyOptionVariance None None None



foreign import data TypVar :: Type -- index
                           -> Type

foreign import data TypForall :: Type -- body
                              -> Type

foreign import data TypArr :: Type -- domain
                           -> Type -- codomain
                           -> Type

foreign import data TypApp :: Type
                           -> Type
                           -> Type

foreign import data TypRef :: Type
                           -> Type

foreign import data TypRef1 :: (Type -> Type)
                            -> Type

foreign import data TypRef2 :: (Type -> Type -> Type)
                            -> Type


type V0 = TypVar Zero
type V1 = TypVar (Succ Zero)


class IsDataType (typ :: Type)
                 (dataTyp :: Type)
                 | typ -> dataTyp
                 , dataTyp -> typ

class IsDataType1 (typ :: Type -> Type)
                  (dataTyp :: Type)
                  | typ -> dataTyp
                  , dataTyp -> typ


class VarianceInTypeExpr (varRef :: Type)
                         (expr :: Type)
                         (varianceOpt :: Type)
                         | varRef expr -> varianceOpt

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

instance varianceInTypeExprRef
  :: VarianceInTypeExpr varRef (TypRef t) None


class VarianceInType (varRef :: Type)
                     (expr :: Type)
                     (variance :: Type)
                     | varRef expr -> variance

instance varianceInType
  :: (VarianceInTypeExpr varRef expr varianceOpt,
      OrElse varianceOpt (Variance True True) variance)
  => VarianceInType varRef expr variance


class VarianceInCtorArgs (varRef :: Type)
                         (list :: Type)
                         (varianceOpt :: Type)
                         | varRef list -> varianceOpt

instance varianceInCtorNil
  :: VarianceInCtorArgs varRef Nil None

instance varianceInCtorCons
  :: (VarianceInTypeExpr varRef head headVariance,
      VarianceInCtorArgs varRef tail tailVariance,
      UnifyOptionVariance headVariance tailVariance varianceOpt)
  => VarianceInCtorArgs varRef (Cons head tail) varianceOpt


class VarianceInCtor (varRef :: Type)
                     (ctor :: Type)
                     (varianceOpt :: Type)
                     | varRef ctor -> varianceOpt

instance varianceInCtor
  :: VarianceInCtorArgs varRef args varianceOpt
  => VarianceInCtor varRef (Ctor name args) varianceOpt


class VarianceInDataTypeCtors (varRef :: Type)
                              (list :: Type)
                              (varianceOpt :: Type)
                              | varRef list -> varianceOpt

instance varianceInDataTypeNil
  :: VarianceInDataTypeCtors varRef Nil None

instance varianceInDataTypeCons
  :: (VarianceInCtor varRef head headVariance,
      VarianceInDataTypeCtors varRef tail tailVariance,
      UnifyOptionVariance headVariance tailVariance varianceOpt)
  => VarianceInDataTypeCtors varRef (Cons head tail) varianceOpt


class VarianceInDataType (varRef :: Type)
                         (dataTyp :: Type)
                         (varianceOpt :: Type)
                         | varRef dataTyp -> varianceOpt

instance varianceInDataType
  :: VarianceInDataTypeCtors varRef ctors varianceOpt
  => VarianceInDataType varRef (DataType typRef params ctors) varianceOpt


class IsFunctor (dataTyp :: Type)
                (outcome :: Boolean)
                | dataTyp -> outcome

instance isFunctor
  :: (GetLast args varRef varKind,
      VarianceInDataTypeCtors varRef ctors varianceOpt,
      OrElse varianceOpt (Variance True True) (Variance pos neg),
      -- must not appear in contravariant position
      Not neg outcome)
  => IsFunctor (DataType typRef args ctors) outcome

checkFunctor :: forall typ dataTyp outcome.
  IsDataType1 typ dataTyp =>
  IsFunctor dataTyp outcome =>
  Proxy2 typ -> BProxy outcome
checkFunctor _ = BProxy


class IsContravariant (dataTyp :: Type)
                      (outcome :: Boolean)
                      | dataTyp -> outcome

instance isContravariant
  :: (GetLast args varRef varKind,
      VarianceInDataTypeCtors varRef ctors varianceOpt,
      OrElse varianceOpt (Variance True True) (Variance pos neg),
      -- must not appear in covariant position
      Not pos outcome)
  => IsContravariant (DataType typRef args ctors) outcome

checkContravariant :: forall typ dataTyp outcome.
  IsDataType1 typ dataTyp =>
  IsContravariant dataTyp outcome =>
  Proxy2 typ -> BProxy outcome
checkContravariant _ = BProxy


checkVariance :: forall varRef typExpr var.
  VarianceInType varRef typExpr var =>
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
     (DataType (DataRef "Data.Maybe" "Maybe") (Cons KindType Nil)
      (Cons (Ctor "Nothing" Nil)
       (Cons (Ctor "Just" (Cons (TypVar Zero) Nil))
        Nil)))

exampleIsFunctorMaybe :: BProxy True
exampleIsFunctorMaybe = checkFunctor (Proxy2 :: Proxy2 Maybe)


data X a = X ((a -> Unit) -> Unit)
instance xDataType
  :: IsDataType1 X
     (DataType (DataRef "Main" "X") (Cons KindType Nil)
      (Cons (Ctor "X" (Cons (TypArr (TypArr (TypVar Zero) (TypRef Unit)) (TypRef Unit)) Nil))
       Nil))

exampleIsFunctorX :: BProxy True
exampleIsFunctorX = checkFunctor (Proxy2 :: Proxy2 X)

exampleIsContravariantX :: BProxy False
exampleIsContravariantX = checkContravariant (Proxy2 :: Proxy2 X)


data Y a = Y (a -> Unit)
instance yDataType
  :: IsDataType1 Y
     (DataType (DataRef "Main" "Y") (Cons KindType Nil)
      (Cons (Ctor "Y" (Cons (TypArr (TypVar Zero) (TypRef Unit)) Nil))
       Nil))

exampleIsFunctorY :: BProxy False
exampleIsFunctorY = checkFunctor (Proxy2 :: Proxy2 Y)

exampleIsContravariantY :: BProxy True
exampleIsContravariantY = checkContravariant (Proxy2 :: Proxy2 Y)


main :: forall e. Eff (console :: CONSOLE | e) Unit
main = do
  log "Hello datatypes!"

