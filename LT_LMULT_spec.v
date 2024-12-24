Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem102614 : forall m : nat, forall n : nat, forall p : nat, ((~ (m = (NUMERAL 0))) /\ (Peano.lt n p)) -> Peano.lt (Nat.mul m n) (Nat.mul m p).
