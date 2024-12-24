Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1245482 : forall m : nat, forall n : nat, forall p : nat, (Nat.mul (dist (@pair nat nat m n)) p) = (dist (@pair nat nat (Nat.mul m p) (Nat.mul n p))).
