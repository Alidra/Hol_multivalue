Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6919131 : forall {_126367 _126408 : Type'}, (forall f : _126367 -> int, (@isum _126367 (@EMPTY _126367) f) = (int_of_num (NUMERAL 0))) /\ (forall x : _126408, forall f : _126408 -> int, forall s : _126408 -> Prop, (@FINITE _126408 s) -> (@isum _126408 (@INSERT _126408 x s) f) = (@COND int (@IN _126408 x s) (@isum _126408 s f) (int_add (f x) (@isum _126408 s f)))).
