open import util

open import Data.List.Base


private
  variable
    l ll l1 l2 l3 : Level
    a b c i f : Level
    A : Set a
    B : Set b
    C : Set c

data TPtr (V : Set l1) (A : Set l2) : Set (l1 ~U~ l2) where
  ptr : V -> TPtr V A


record Memory (V : Set l1) (MEM : Set l1 -> Set (l1 ~U~ l2) -> Set l3) : Set (lsuc (l1 ~U~ l2 ~U~ l3)) where
  field
    empty : MEM V A
    new : {A : Set l2} -> (a : A) -> MEM V (TPtr V A)
    get : (TPtr V A) -> MEM V A



IFun : (l : Level) -> Set (lsuc l)
IFun l = Set l -> Set l

------------------------------------------------------------------------
-- Type, and usual combinators

record RawIApplicative (F : IFun f) :
                       Set (i ~U~ lsuc f) where
  infixl 4 _⊛_

  field
    pure : A -> F A
    _⊛_  : F (A -> B) -> F A -> F B

{-
record MemoryMonadLaws {V : Set l} (MEM : MemType l1 l2) {{Memory MEM}} {{Monad (MEM V))}} where
  field
    --TODO: make sure pointers are conserved during state change
-}

record Mergeable (A : Set l) : Set l where
  field
    merge : A -> A -> A
