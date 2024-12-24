Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3112880 : forall n : nat, forall d : nat, forall e : nat, ((num_divides d n) /\ ((n = (NUMERAL 0)) -> e = (NUMERAL 0))) -> (num_divides (Nat.div n d) e) = (num_divides n (Nat.mul d e)).
