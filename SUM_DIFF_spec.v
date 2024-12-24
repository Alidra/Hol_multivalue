Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7068309 : forall {_131590 : Type'}, forall f : _131590 -> real, forall s : _131590 -> Prop, forall t : _131590 -> Prop, ((@FINITE _131590 s) /\ (@SUBSET _131590 t s)) -> (@sum _131590 (@DIFF _131590 s t) f) = (real_sub (@sum _131590 s f) (@sum _131590 t f)).
