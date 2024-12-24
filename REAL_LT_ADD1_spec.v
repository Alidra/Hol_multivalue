Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1504643 : forall x : real, forall y : real, (real_le x y) -> real_lt x (real_add y (real_of_num (NUMERAL (BIT1 0)))).
