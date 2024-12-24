Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1490175 : forall x : real, forall y : real, ((real_add x y) = (real_of_num (NUMERAL 0))) = (x = (real_neg y)).
