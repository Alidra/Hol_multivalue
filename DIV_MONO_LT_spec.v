Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem195907 : forall m : nat, forall n : nat, forall p : nat, ((~ (p = (NUMERAL 0))) /\ (Peano.le (Nat.add m p) n)) -> Peano.lt (Nat.div m p) (Nat.div n p).
