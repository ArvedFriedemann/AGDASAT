module util where

open import Agda.Primitive

import Relation.Binary.PropositionalEquality as Eqiv
open Eqiv using (_≡_; refl; trans; sym; cong; cong-app; subst) public
open Eqiv.≡-Reasoning using (begin_; _≡⟨⟩_; step-≡; step-≡˘; _∎) public

-- private
variable
  l : Level

_===_ = _≡_
_=<>_ = _≡⟨⟩_
_end = _∎

infix  3 _end
infixr 2 _=<>_ _=<_>_ _=^<_>_

_=<_>_ : forall {a} {A : Set a} (x {y z} : A) -> y === z -> x === y -> x === z
a =< b > c =  a ≡⟨ c ⟩ b

_=^<_>_ : forall {a} {A : Set a} (x {y z} : A) -> y === z -> y === x -> x === z
a =^< b > c =  a ≡˘⟨ c ⟩ b


data BOT {l} : Set l where


infix 3 ¬_
¬_ : {e : Level} ->  Set e -> Set e
¬ prop = prop -> BOT

data Bool {l} : Set l where
  true : Bool
  false : Bool


ite : {A : Set l} -> Bool -> A -> A -> A
ite true a _ = a
ite false _ b = b

not : Bool -> Bool
not true = false
not false = true

dub-not-id : forall {b : Bool} -> not (not b) === b
dub-not-id {true} = refl
dub-not-id {false} = refl

dub-not-id' : forall {b : Bool} -> b === not (not b)
dub-not-id' = sym dub-not-id

switch-not : forall {b c : Bool} -> not b === c -> b === not c
switch-not ¬b=c = trans dub-not-id' (cong not ¬b=c)

switch-not' : forall {b c : Bool} -> b === not c -> not b === c
switch-not' b=¬c = sym (switch-not (sym b=¬c))


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

open sigma public

infixr 1 _or_
data _or_ (A B : Set) : Set where
  left : A -> A or B
  right : B -> A or B

open _or_ public

const : {A B : Set} -> A -> B -> A
const x _ = x

record Eq {a} (A : Set a) : Set a where
  field
    _==_ : A -> A -> Bool

open Eq {{...}} public

idfrID : {A B : Set l} -> {{_ : Eq A}} -> A -> B -> B -> A -> B
idfrID i a b i' = ite (i == i') a b
