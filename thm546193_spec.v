Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem546193 : forall (m : nat) (n : nat), (fun n' : nat => (Nat.add (BIT1 m) (BIT1 n')) = (BIT0 (S (Nat.add m n')))) n.
