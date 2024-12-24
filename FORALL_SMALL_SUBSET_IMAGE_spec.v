Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4075307 : forall {_102373 _102400 : Type'}, forall P : (_102400 -> Prop) -> Prop, forall f : _102373 -> _102400, forall s : _102373 -> Prop, forall n : nat, (forall t : _102400 -> Prop, ((@FINITE _102400 t) /\ ((Peano.lt (@CARD _102400 t) n) /\ (@SUBSET _102400 t (@IMAGE _102373 _102400 f s)))) -> P t) = (forall t : _102373 -> Prop, ((@FINITE _102373 t) /\ ((Peano.lt (@CARD _102373 t) n) /\ (@SUBSET _102373 t s))) -> P (@IMAGE _102373 _102400 f t)).
