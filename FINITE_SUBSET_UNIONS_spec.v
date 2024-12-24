Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3756509 : forall {A : Type'}, forall f : (A -> Prop) -> Prop, forall s : A -> Prop, ((@FINITE A s) /\ (@SUBSET A s (@UNIONS A f))) -> exists f' : (A -> Prop) -> Prop, (@FINITE (A -> Prop) f') /\ ((@SUBSET (A -> Prop) f' f) /\ (@SUBSET A s (@UNIONS A f'))).
