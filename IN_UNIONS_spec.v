Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3205091 : forall {A : Type'}, forall s : (A -> Prop) -> Prop, forall x : A, (@IN A x (@UNIONS A s)) = (exists t : A -> Prop, (@IN (A -> Prop) t s) /\ (@IN A x t)).