Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2307626 : forall x : int, (int_pow x (NUMERAL (BIT1 0))) = x.
