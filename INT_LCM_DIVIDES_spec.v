Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2826831 : forall m : int, forall n : int, forall d : int, (int_divides (int_lcm (@pair int int m n)) d) = ((int_divides m d) /\ (int_divides n d)).
