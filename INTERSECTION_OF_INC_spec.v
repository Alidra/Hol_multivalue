Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4842609 : forall {A : Type'}, forall P : ((A -> Prop) -> Prop) -> Prop, forall Q : (A -> Prop) -> Prop, forall s : A -> Prop, ((P (@INSERT (A -> Prop) s (@EMPTY (A -> Prop)))) /\ (Q s)) -> @INTERSECTION_OF A P Q s.
