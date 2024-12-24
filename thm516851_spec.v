Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem516851 : forall (m : nat) (n : nat) (p : nat), (fun p' : nat => (Peano.le (Nat.mul m n) (Nat.mul m p')) = ((m = (NUMERAL 0)) \/ (Peano.le n p'))) p.
