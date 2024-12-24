Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6905935 : (@ε int (fun x : int => forall y : int, ((int_mul x y) = y) /\ ((int_mul y x) = y))) = (int_of_num (NUMERAL (BIT1 0))).
