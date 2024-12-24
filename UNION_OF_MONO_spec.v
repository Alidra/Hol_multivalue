Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4844116 : forall {A : Type'}, forall P : ((A -> Prop) -> Prop) -> Prop, forall Q : (A -> Prop) -> Prop, forall Q' : (A -> Prop) -> Prop, forall s : A -> Prop, ((@UNION_OF A P Q s) /\ (forall x : A -> Prop, (Q x) -> Q' x)) -> @UNION_OF A P Q' s.
