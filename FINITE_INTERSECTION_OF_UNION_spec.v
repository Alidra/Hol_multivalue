Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4895351 : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (forall s : A -> Prop, forall t : A -> Prop, ((P s) /\ (P t)) -> P (@UNION A s t)) -> forall s : A -> Prop, forall t : A -> Prop, ((@INTERSECTION_OF A (@FINITE (A -> Prop)) P s) /\ (@INTERSECTION_OF A (@FINITE (A -> Prop)) P t)) -> @INTERSECTION_OF A (@FINITE (A -> Prop)) P (@UNION A s t).
