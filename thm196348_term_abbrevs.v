Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> ((Nat.div y0 y1) = (NUMERAL 0)) = (Peano.lt y0 y1).
