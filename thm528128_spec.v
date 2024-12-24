Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem528128 : forall (m : nat) (n : nat), (fun n' : nat => (Nat.add (BIT1 m) (BIT0 n')) = (BIT1 (Nat.add m n'))) n.
