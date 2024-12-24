Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4887037 : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall u : (A -> Prop) -> Prop, ((@FINITE (A -> Prop) u) /\ (forall s : A -> Prop, (@IN (A -> Prop) s u) -> @UNION_OF A (@FINITE (A -> Prop)) P s)) -> @UNION_OF A (@FINITE (A -> Prop)) P (@UNIONS A u).
