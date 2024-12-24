Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7067826 : forall {_131550 : Type'}, forall f : _131550 -> real, forall s : _131550 -> Prop, forall t : _131550 -> Prop, ((@FINITE _131550 s) /\ ((@FINITE _131550 t) /\ (@DISJOINT _131550 s t))) -> (@sum _131550 (@UNION _131550 s t) f) = (real_add (@sum _131550 s f) (@sum _131550 t f)).
