Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := forall y0 : int, forall y1 : int, forall y2 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (rem y0 (int_mul y1 y2)) = (int_add (int_mul y1 (rem (div y0 y1) y2)) (rem y0 y1)).
