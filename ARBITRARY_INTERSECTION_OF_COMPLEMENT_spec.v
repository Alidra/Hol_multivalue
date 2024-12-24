Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4860962 : forall {A : Type'}, forall P : (A -> Prop) -> Prop, forall s : A -> Prop, (@INTERSECTION_OF A (@ARBITRARY A) P s) = (@UNION_OF A (@ARBITRARY A) (fun s' : A -> Prop => P (@DIFF A (@UNIV A) s')) (@DIFF A (@UNIV A) s)).
