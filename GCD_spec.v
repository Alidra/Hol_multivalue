Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3133024 : forall a : nat, forall b : nat, ((num_divides (num_gcd (@pair nat nat a b)) a) /\ (num_divides (num_gcd (@pair nat nat a b)) b)) /\ (forall e : nat, ((num_divides e a) /\ (num_divides e b)) -> num_divides e (num_gcd (@pair nat nat a b))).
