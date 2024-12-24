Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2300922 : forall a : int, forall b : int, forall c : int, forall d : int, (int_sub (int_add a b) (int_add c d)) = (int_add (int_sub a c) (int_sub b d)).
