module versat where

data BOT : Set where

infix 3 ¬_
¬_ : Set -> Set
¬ prop = prop -> BOT

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

infixr 1 _or_
data _or_ (A B : Set) : Set where
  left : A -> A or B
  right : B -> A or B

data _===_ {A : Set} (x : A) : A -> Set where
  refl : x === x

const : {A B : Set} -> A -> B -> A
const x _ = x

data Formula (X : Set) : Set where
  top : Formula X
  bot : Formula X
  val : X -> Formula X
  neg : Formula X -> Formula X
  _^_ : Formula X -> Formula X -> Formula X
  _v_ : Formula X -> Formula X -> Formula X

eval : {X : Set} -> (X -> Bool) -> Formula X -> Bool
eval _ top = true
eval _ bot = false
eval fkt (val x) = fkt x
eval fkt (neg f) = not (eval fkt f)
eval fkt (a ^ b) = (eval fkt a) && (eval fkt b)
eval fkt (a v b) = (eval fkt a) || (eval fkt b)

solver : {A : Set} -> (aim : Bool) -> (f : Formula A) -> (exists m of (A -> Bool) st (eval m f === aim) ) or (forall (m : A -> Bool) -> ¬ (eval m f === aim) )

solver true top = left < const false , refl >
solver false top = right (\m ())
solver false bot = left < const false , refl >
solver true bot = right (\m ())

solver aim (val x) = left < const aim , refl >

solver aim (neg f) = {! !}
solver aim (a ^ b) = {! !}
solver aim (a v b) = {! !}
