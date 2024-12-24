Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem515685 : forall (m : nat), (fun m' : nat => (Nat.pow m' 0) = (BIT1 0)) m.
