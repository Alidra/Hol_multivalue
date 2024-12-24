Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7064171 : ((@ε real (fun x : real => forall y : real, ((real_add x y) = y) /\ ((real_add y x) = y))) = (real_of_num (NUMERAL 0))) = ((@neutral real real_add) = (real_of_num (NUMERAL 0))).
