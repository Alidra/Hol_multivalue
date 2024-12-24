Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem516742 : forall (m : nat) (n : nat) (p : nat), (fun p' : nat => (Peano.lt (Nat.mul m n) (Nat.mul m p')) = ((~ (m = (NUMERAL 0))) /\ (Peano.lt n p'))) p.
