Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2816478 : forall m : int, forall n : int, forall d : int, (int_divides d (int_lcm (@pair int int m n))) = (int_divides (int_mul d (int_gcd (@pair int int m n))) (int_mul m n)).
