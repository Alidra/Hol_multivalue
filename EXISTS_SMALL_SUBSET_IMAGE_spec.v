Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4074677 : forall {_102289 _102316 : Type'}, forall P : (_102316 -> Prop) -> Prop, forall f : _102289 -> _102316, forall s : _102289 -> Prop, forall n : nat, (exists t : _102316 -> Prop, (@FINITE _102316 t) /\ ((Peano.lt (@CARD _102316 t) n) /\ ((@SUBSET _102316 t (@IMAGE _102289 _102316 f s)) /\ (P t)))) = (exists t : _102289 -> Prop, (@FINITE _102289 t) /\ ((Peano.lt (@CARD _102289 t) n) /\ ((@SUBSET _102289 t s) /\ (P (@IMAGE _102289 _102316 f t))))).
