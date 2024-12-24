Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem245931 : forall P : nat -> Prop, forall n : nat, (~ (n = (NUMERAL 0))) -> (exists a : nat, P (Nat.modulo a n)) = (exists a : nat, (Peano.lt a n) /\ (P a)).
