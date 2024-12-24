Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1247096 : forall m : nat, forall n : nat, forall p : nat, (Peano.le (dist (@pair nat nat m n)) p) = ((Peano.le m (Nat.add n p)) /\ (Peano.le n (Nat.add m p))).
