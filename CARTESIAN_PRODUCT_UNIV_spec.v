Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4432579 : forall {A K : Type'}, (@cartesian_product A K (@UNIV K) (fun i : K => @UNIV A)) = (@UNIV (K -> A)).
