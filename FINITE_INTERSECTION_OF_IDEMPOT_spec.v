Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4886898 : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (@INTERSECTION_OF A (@FINITE (A -> Prop)) (@INTERSECTION_OF A (@FINITE (A -> Prop)) P)) = (@INTERSECTION_OF A (@FINITE (A -> Prop)) P).
