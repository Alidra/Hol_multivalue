Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1247478 : forall (d : nat) (m : nat) (n : nat) (d' : nat) (h1 : m = (Nat.add n d')), (Peano.le d (Nat.add d' (dist (@pair nat nat n (Nat.add (Nat.add n d') d))))) = (Peano.le d (Nat.add d' (dist (@pair nat nat n (Nat.add m d))))).
