Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7067645 : forall {_131483 _131524 : Type'}, (forall f : _131483 -> real, (@sum _131483 (@EMPTY _131483) f) = (real_of_num (NUMERAL 0))) /\ (forall x : _131524, forall f : _131524 -> real, forall s : _131524 -> Prop, (@FINITE _131524 s) -> (@sum _131524 (@INSERT _131524 x s) f) = (@COND real (@IN _131524 x s) (@sum _131524 s f) (real_add (f x) (@sum _131524 s f)))).
