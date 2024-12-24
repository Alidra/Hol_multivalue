Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4890889 : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (forall s : A -> Prop, forall t : A -> Prop, ((P s) /\ (P t)) -> P (@INTER A s t)) -> forall s : A -> Prop, forall t : A -> Prop, ((@UNION_OF A (@FINITE (A -> Prop)) P s) /\ (@UNION_OF A (@FINITE (A -> Prop)) P t)) -> @UNION_OF A (@FINITE (A -> Prop)) P (@INTER A s t).
