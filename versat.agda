module versat where

data Bool : Set where
  true : Bool
  false : Bool

not : Bool -> Bool
not true = false
not false = true

_&&_ : Bool -> Bool -> Bool
_&&_ true true = true
_&&_ _ _ = false

_||_ : Bool -> Bool -> Bool
_||_ false false = false
_||_ _ _ = true

data sigma (A : Set) (B : A -> Set) : Set where
  <_,_> : (x : A) -> B x -> sigma A B

sigma-syntax = sigma
infix 2 sigma-syntax
syntax sigma-syntax A (\ x -> B) = exists x of A st B

data _or_ (A B : Set) : Set where
  left : A -> A or B
  right : B -> A or B

data _===_ {A : Set} (x : A) : A -> Set where
  refl : x === x

data BOT : Set where

data Formula (X : Set) : Set where
  top : Formula X
  bot : Formula X
  val : X -> Formula X
  neg : Formula X -> Formula X
  _^_ : Formula X -> Formula X -> Formula X
  _v_ : Formula X -> Formula X -> Formula X

{-
eval : {X : Set} -> (X -> Bool) -> Formula X -> Bool
eval _ top = true
eval _ bot = false
eval fkt (val x) = fkt x
eval fkt (neg f) = not (eval fkt f)
eval fkt (a ^ b) = (eval fkt a) && (eval fkt b)
eval fkt (a v b) = (eval fkt a) || (eval fkt b)
-}

solver-creation : {X A : Set} ->
                  (evalfkt : (X -> A) -> Formula X -> A) ->
                  exists solver of (Formula X -> A -> (X -> A)) st
                    ((f : Formula X) (a : A) ->
                      (evalfkt (solver f a) f === a) or
                      ((model : X -> A) -> evalfkt model f === a -> BOT) )
solver-creation evalfkt = {! !}
