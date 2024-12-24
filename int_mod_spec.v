Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2437408 : forall n : int, forall x : int, forall y : int, (int_mod n x y) = (int_divides n (int_sub x y)).
