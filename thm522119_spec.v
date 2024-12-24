Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem522119 : forall (m : nat), (fun m' : nat => (S m') = (Nat.add m' (NUMERAL (BIT1 0)))) m.
