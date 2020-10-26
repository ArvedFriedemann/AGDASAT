module util where


open import Agda.Primitive renaming (_⊔_ to _~U~_ ) public

import Relation.Binary.PropositionalEquality as Eqality
open Eqality using (refl; trans; sym; cong; cong-app; subst) renaming (_≡_ to _===_) public
open Eqality.≡-Reasoning using (begin_; step-≡; step-≡˘) renaming (_≡⟨⟩_ to _=<>_ ; _∎ to _end) public

private
  variable
    l ll l1 l2 : Level

infixr 2 _=<_>_ _=^<_>_

_=<_>_ : forall {a} {A : Set a} (x {y z} : A) -> y === z -> x === y -> x === z
a =< b > c =  a ≡⟨ c ⟩ b

_=^<_>_ : forall {a} {A : Set a} (x {y z} : A) -> y === z -> y === x -> x === z
a =^< b > c =  a ≡˘⟨ c ⟩ b


data BOT {l} : Set l where
data TOP {l} : Set l where
  <> : TOP

infix 3 ¬_
¬_ : Set l -> Set (lsuc l)
¬ prop = prop -> BOT

data Bool {l} : Set l where
  true : Bool {l}
  false : Bool {l}

not : Bool {l} -> Bool {l}
not true = false
not false = true

dub-not-id : forall {l} {b : Bool {l}} -> not (not b) === b
dub-not-id {l} {true} = refl
dub-not-id {l} {false} = refl

dub-not-id' : forall {l} {b : Bool {l}} -> b === not (not b)
dub-not-id' = sym dub-not-id

switch-not : forall {l} {b c : Bool {l}} -> not b === c -> b === not c
switch-not ¬b=c = trans dub-not-id' (cong not ¬b=c)

switch-not' : forall {l} {b c : Bool {l}} -> b === not c -> not b === c
switch-not' b=¬c = sym (switch-not (sym b=¬c))


_&&_ : Bool {l} -> Bool {ll} -> Bool {l ~U~ ll}
_&&_ true true = true
_&&_ _ _ = false

_||_ : Bool {l} -> Bool {ll} -> Bool {l ~U~ ll}
_||_ false false = false
_||_ _ _ = true

data sigma (A : Set l) (B : A -> Set ll) : Set (l ~U~ ll) where
  <_,_> : (x : A) -> B x -> sigma A B

sigma-syntax = sigma
infix 2 sigma-syntax
syntax sigma-syntax A (\ x -> B) = exists x of A st B

infixr 1 _or_
data _or_ (A B : Set l) : Set l where
  left : A -> A or B
  right : B -> A or B

const : {A : Set l1} {B : Set l2} -> A -> B -> A
const x _ = x

absurd : {A : Set l} -> BOT {l} -> A
absurd ()


record Eq (A : Set l) : Set l where
  field
    _==_ : A -> A -> Bool {l}

record Monad (M : Set l -> Set l) : Set (lsuc l) where
  field
    return : {A : Set l} -> A -> M A
    _>>=_ : {A B : Set l} -> M A -> (A -> M B) -> M B

  _>>_ : {A B : Set l} -> M A -> M B -> M B
  ma >> mb = ma >>= const mb
