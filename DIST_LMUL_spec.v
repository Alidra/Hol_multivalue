Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1245388 : forall m : nat, forall n : nat, forall p : nat, (Nat.mul m (dist (@pair nat nat n p))) = (dist (@pair nat nat (Nat.mul m n) (Nat.mul m p))).
