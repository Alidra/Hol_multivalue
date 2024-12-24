Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem538283 : forall (m : nat) (n : nat), (fun n' : nat => (Nat.add (BIT0 m) (BIT1 n')) = (BIT1 (Nat.add m n'))) n.
