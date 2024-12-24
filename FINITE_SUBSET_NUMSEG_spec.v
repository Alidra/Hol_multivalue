Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5379224 : forall s : nat -> Prop, (@FINITE nat s) = (exists n : nat, @SUBSET nat s (dotdot (NUMERAL 0) n)).
