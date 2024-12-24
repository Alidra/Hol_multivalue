Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem513166 : forall (m : nat) (n : nat), (fun n' : nat => (Nat.add m (S n')) = (S (Nat.add m n'))) n.
