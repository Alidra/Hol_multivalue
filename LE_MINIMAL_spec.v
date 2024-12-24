Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem276690 : forall P : nat -> Prop, forall n : nat, (exists r : nat, P r) -> (Peano.le n (minimal P)) = (forall i : nat, (P i) -> Peano.le n i).
