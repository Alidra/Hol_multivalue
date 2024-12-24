Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3112549 : forall m : nat, forall n : nat, (num_divides m n) = ((Nat.mul (Nat.div n m) m) = n).
