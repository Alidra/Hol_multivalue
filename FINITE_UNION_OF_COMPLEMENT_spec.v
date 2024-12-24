Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4879265 : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, (@UNION_OF A (@FINITE (A -> Prop)) P s) = (@INTERSECTION_OF A (@FINITE (A -> Prop)) (fun s' : A -> Prop => P (@DIFF A (@UNIV A) s')) (@DIFF A (@UNIV A) s)).
