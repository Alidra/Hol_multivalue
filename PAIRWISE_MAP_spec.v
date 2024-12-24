Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1231297 : forall {A B : Type'}, forall R : B -> B -> Prop, forall f : A -> B, forall l : list A, (@List.ForallOrdPairs B R (@List.map A B f l)) = (@List.ForallOrdPairs A (fun x : A => fun y : A => R (f x) (f y)) l).
