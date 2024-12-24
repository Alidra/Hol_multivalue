Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4860847 : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, (@UNION_OF A (@ARBITRARY A) P s) = (@INTERSECTION_OF A (@ARBITRARY A) (fun s' : A -> Prop => P (@DIFF A (@UNIV A) s')) (@DIFF A (@UNIV A) s)).
