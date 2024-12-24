Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3169490 : forall n : int, (real_zpow (real_of_num (NUMERAL (BIT1 0))) n) = (real_of_num (NUMERAL (BIT1 0))).
