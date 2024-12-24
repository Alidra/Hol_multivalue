Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4434827 : forall {A K : Type'}, forall k : K -> Prop, forall x : K -> A, (@EXTENSIONAL K A k x) -> (@cartesian_product A K k (fun i : K => @INSERT A (x i) (@EMPTY A))) = (@INSERT (K -> A) x (@EMPTY (K -> A))).
