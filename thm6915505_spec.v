Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6915505 : (@ε int (fun x : int => forall y : int, ((int_add x y) = y) /\ ((int_add y x) = y))) = (int_of_num (NUMERAL 0)).
