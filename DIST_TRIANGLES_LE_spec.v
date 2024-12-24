Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1260086 : forall m : nat, forall n : nat, forall p : nat, forall q : nat, forall r : nat, forall s : nat, ((Peano.le (dist (@pair nat nat m n)) r) /\ (Peano.le (dist (@pair nat nat p q)) s)) -> Peano.le (dist (@pair nat nat m p)) (Nat.add (dist (@pair nat nat n q)) (Nat.add r s)).
