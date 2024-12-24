Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem546215 : forall (m : nat) (n : nat), ((fun n' : nat => (Nat.add (BIT0 m) (BIT0 n')) = (BIT0 (Nat.add m n'))) n) = ((Nat.add (BIT0 m) (BIT0 n)) = (BIT0 (Nat.add m n))).
