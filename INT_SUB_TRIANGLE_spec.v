Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2310536 : forall a : int, forall b : int, forall c : int, (int_add (int_sub a b) (int_sub b c)) = (int_sub a c).
