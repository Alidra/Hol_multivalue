Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3855272 : forall {A : Type'}, forall a : A, (@CARD A (@INSERT A a (@EMPTY A))) = (NUMERAL (BIT1 0)).
