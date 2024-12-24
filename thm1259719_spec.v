Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1259719 : forall m : nat, forall n : nat, forall p : nat, Peano.le (dist (@pair nat nat m p)) (Nat.add (dist (@pair nat nat m n)) (dist (@pair nat nat n p))).
