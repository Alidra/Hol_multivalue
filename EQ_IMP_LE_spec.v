Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem98471 : forall m : nat, forall n : nat, (m = n) -> Peano.le m n.
