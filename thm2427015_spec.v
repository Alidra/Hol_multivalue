Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2427015 : forall (a : int) (d : int) (b : int) (c : int), ((fun d' : int => ((~ (a = b)) /\ (~ (c = d'))) = (~ ((int_add (int_mul a c) (int_mul b d')) = (int_add (int_mul a d') (int_mul b c))))) d) = (((~ (a = b)) /\ (~ (c = d))) = (~ ((int_add (int_mul a c) (int_mul b d)) = (int_add (int_mul a d) (int_mul b c))))).
