Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1999793 : forall (x : real) (y : real), (~ ((real_lt x y) = ((real_lt x y) /\ (~ (x = y))))) -> False.
