Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1247464 : forall (n : nat) (m : nat) (d : nat), (forall d' : nat, ((m = (Nat.add n d')) -> Peano.le d (Nat.add d' (dist (@pair nat nat n (Nat.add m d))))) /\ ((n = (Nat.add m d')) -> Peano.le d (Nat.add d' (dist (@pair nat nat n (Nat.add m d)))))) = (Peano.le d (Nat.add (dist (@pair nat nat m n)) (dist (@pair nat nat n (Nat.add m d))))).
