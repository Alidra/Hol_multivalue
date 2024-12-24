Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3693974 : forall {_93804 _93824 : Type'}, forall P : (_93824 -> Prop) -> Prop, forall f : _93804 -> _93824, forall s : _93804 -> Prop, (exists t : _93824 -> Prop, (@FINITE _93824 t) /\ ((@SUBSET _93824 t (@IMAGE _93804 _93824 f s)) /\ (P t))) = (exists t : _93804 -> Prop, (@FINITE _93804 t) /\ ((@SUBSET _93804 t s) /\ (P (@IMAGE _93804 _93824 f t)))).
