Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1259675 : forall (m : nat), forall n : nat, forall p : nat, forall q : nat, Peano.le (dist (@pair nat nat m p)) (Nat.add (dist (@pair nat nat (Nat.add m n) (Nat.add p q))) (dist (@pair nat nat n q))).
