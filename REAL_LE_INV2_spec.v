Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1632440 : forall x : real, forall y : real, ((real_lt (real_of_num (NUMERAL 0)) x) /\ (real_le x y)) -> real_le (real_inv y) (real_inv x).
