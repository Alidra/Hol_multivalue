Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4067239 : forall {_102126 _102133 : Type'}, forall P : (_102133 -> Prop) -> Prop, forall f : _102126 -> _102133, forall s : _102126 -> Prop, forall n : nat, (exists t : _102133 -> Prop, (@FINITE _102133 t) /\ ((Peano.lt (@CARD _102133 t) n) /\ ((@SUBSET _102133 t (@IMAGE _102126 _102133 f s)) /\ (P t)))) = (exists t : _102126 -> Prop, (@FINITE _102126 t) /\ ((Peano.lt (@CARD _102126 t) n) /\ ((@SUBSET _102126 t s) /\ ((forall x : _102126, forall y : _102126, ((@IN _102126 x t) /\ (@IN _102126 y t)) -> ((f x) = (f y)) = (x = y)) /\ (P (@IMAGE _102126 _102133 f t)))))).
