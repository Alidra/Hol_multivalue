Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4879380 : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, (@INTERSECTION_OF A (@FINITE (A -> Prop)) P s) = (@UNION_OF A (@FINITE (A -> Prop)) (fun s' : A -> Prop => P (@DIFF A (@UNIV A) s')) (@DIFF A (@UNIV A) s)).
