Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2416513 : forall (a : int) (b : int) (m : int), (int_add (int_mul a m) (int_mul b m)) = (int_mul (int_add a b) m).
