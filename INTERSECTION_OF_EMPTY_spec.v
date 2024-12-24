Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4851880 : forall {A : Type'}, forall P : ((A -> Prop) -> Prop) -> Prop, forall Q : (A -> Prop) -> Prop, (P (@EMPTY (A -> Prop))) -> @INTERSECTION_OF A P Q (@UNIV A).
