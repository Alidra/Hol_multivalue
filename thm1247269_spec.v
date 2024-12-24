Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1247269 : forall (n : nat) (p : nat) (m : nat) (d : nat) (h1 : p = (Nat.add m d)), (Peano.le d (Nat.add (dist (@pair nat nat m n)) (dist (@pair nat nat n (Nat.add m d))))) = (Peano.le d (Nat.add (dist (@pair nat nat m n)) (dist (@pair nat nat n p)))).
