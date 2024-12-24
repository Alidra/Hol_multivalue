Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4868151 : forall {A : Type'}, forall P : (A -> Prop) -> Prop, (@UNION_OF A (@ARBITRARY A) (@UNION_OF A (@ARBITRARY A) P)) = (@UNION_OF A (@ARBITRARY A) P).
