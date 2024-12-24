Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem170673 : forall m : nat, forall n : nat, (Peano.lt m n) -> (Nat.modulo m n) = m.
