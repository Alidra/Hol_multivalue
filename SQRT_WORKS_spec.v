Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1943636 : forall x : real, (real_le (real_of_num (NUMERAL 0)) x) -> (real_le (real_of_num (NUMERAL 0)) (sqrt x)) /\ ((real_pow (sqrt x) (NUMERAL (BIT0 (BIT1 0)))) = x).