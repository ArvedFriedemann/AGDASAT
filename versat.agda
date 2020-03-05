module versat where

open import util

open import Agda.Primitive
import Relation.Binary.PropositionalEquality as Eq
open Eq using (refl; trans; sym; cong; cong-app; subst) renaming (_≡_ to _===_)

private
  variable
    l : Level

data Formula (X : Set l) : Set l where
  top : Formula X
  bot : Formula X
  val : X -> Formula X
  neg : Formula X -> Formula X
  _^_ : Formula X -> Formula X -> Formula X
  _v_ : Formula X -> Formula X -> Formula X

eval : {X : Set l} -> (X -> Bool) -> Formula X -> Bool
eval _ top = true
eval _ bot = false
eval fkt (val x) = fkt x
eval fkt (neg f) = not (eval fkt f)
eval fkt (a ^ b) = (eval fkt a) && (eval fkt b)
eval fkt (a v b) = (eval fkt a) || (eval fkt b)

solver : {A : Set l} -> (aim : Bool) -> (f : Formula A) -> (exists m of (A -> Bool) st (eval m f === aim) ) or (forall (m : A -> Bool) -> ¬ (eval m f === aim) )

solver true top = left < const false , refl >
solver false top = right (\m ())
solver false bot = left < const false , refl >
solver true bot = right (\m ())

solver aim (val x) = left < const aim , refl >

solver aim (neg f) with solver (not aim) f
...                 | left < m , oppeq >  = left < m , switch-not' oppeq >
...                 | right unsat = right (\m eq -> unsat m (switch-not eq) )
solver aim (a ^ b) = {! !}
solver aim (a v b) = {! !}
