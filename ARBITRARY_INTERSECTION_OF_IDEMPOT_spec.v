Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4868382 : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (@INTERSECTION_OF A (@ARBITRARY A) (@INTERSECTION_OF A (@ARBITRARY A) P)) = (@INTERSECTION_OF A (@ARBITRARY A) P).
