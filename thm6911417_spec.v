Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6911417 : (@ε real (fun x : real => forall y : real, ((real_mul x y) = y) /\ ((real_mul y x) = y))) = (real_of_num (NUMERAL (BIT1 0))).
