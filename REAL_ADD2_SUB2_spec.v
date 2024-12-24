Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1517635 : forall a : real, forall b : real, forall c : real, forall d : real, (real_sub (real_add a b) (real_add c d)) = (real_add (real_sub a c) (real_sub b d)).
