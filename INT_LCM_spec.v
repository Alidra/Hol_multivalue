Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2829046 : forall m : int, forall n : int, (int_divides m (int_lcm (@pair int int m n))) /\ ((int_divides n (int_lcm (@pair int int m n))) /\ (forall d : int, ((int_divides m d) /\ (int_divides n d)) -> int_divides (int_lcm (@pair int int m n)) d)).
