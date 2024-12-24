Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem522126 : forall (n : nat) (m : nat), ((fun n' : nat => (Peano.le m n') = (exists d : nat, n' = (Nat.add m d))) n) = ((Peano.le m n) = (exists d : nat, n = (Nat.add m d))).
