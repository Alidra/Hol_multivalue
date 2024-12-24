Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4842239 : forall {A : Type'}, forall P : ((A -> Prop) -> Prop) -> Prop, forall Q : (A -> Prop) -> Prop, (@INTERSECTION_OF A P Q) = (fun s : A -> Prop => exists u : (A -> Prop) -> Prop, (P u) /\ ((forall c : A -> Prop, (@IN (A -> Prop) c u) -> Q c) /\ ((@INTERS A u) = s))).
