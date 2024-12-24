Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1246903 : forall (n : nat) (m : nat), ((fun n' : nat => (Peano.lt m n') = (exists d : nat, n' = (Nat.add m (S d)))) n) = ((Peano.lt m n) = (exists d : nat, n = (Nat.add m (S d)))).
