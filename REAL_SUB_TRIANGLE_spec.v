Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1520119 : forall a : real, forall b : real, forall c : real, (real_add (real_sub a b) (real_sub b c)) = (real_sub a c).
