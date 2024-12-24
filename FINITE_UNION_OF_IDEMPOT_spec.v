Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4886667 : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (@UNION_OF A (@FINITE (A -> Prop)) (@UNION_OF A (@FINITE (A -> Prop)) P)) = (@UNION_OF A (@FINITE (A -> Prop)) P).
