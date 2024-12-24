Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4845623 : forall {A : Type'}, forall P : ((A -> Prop) -> Prop) -> Prop, forall Q : (A -> Prop) -> Prop, forall Q' : (A -> Prop) -> Prop, forall s : A -> Prop, ((@INTERSECTION_OF A P Q s) /\ (forall x : A -> Prop, (Q x) -> Q' x)) -> @INTERSECTION_OF A P Q' s.
