Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1332639 : forall x : prod hreal hreal, (~ (treal_eq x (treal_of_num (NUMERAL 0)))) -> treal_eq (treal_mul (treal_inv x) x) (treal_of_num (NUMERAL (BIT1 0))).
