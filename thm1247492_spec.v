Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1247492 : forall (d : nat) (n : nat) (m : nat) (d' : nat) (h1 : n = (Nat.add m d')), (Peano.le d (Nat.add d' (dist (@pair nat nat (Nat.add m d') (Nat.add m d))))) = (Peano.le d (Nat.add d' (dist (@pair nat nat n (Nat.add m d))))).
