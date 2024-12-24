Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2625416 : forall m : int, forall n : int, forall p : int, (int_le (int_of_num (NUMERAL 0)) n) -> (div (div m n) p) = (div m (int_mul n p)).
