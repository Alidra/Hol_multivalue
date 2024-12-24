Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2310253 : forall x : int, forall y : int, (int_sub (int_neg x) y) = (int_neg (int_add x y)).
