Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem528240 : forall (n : nat), (fun n' : nat => (Nat.add 0 (BIT1 n')) = (BIT1 n')) n.
