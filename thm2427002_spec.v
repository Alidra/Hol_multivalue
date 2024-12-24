Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2427002 : (forall a : int, forall b : int, forall c : int, forall d : int, ((~ (a = b)) /\ (~ (c = d))) = (~ ((int_add (int_mul a c) (int_mul b d)) = (int_add (int_mul a d) (int_mul b c))))) /\ (forall n : int, forall a : int, forall b : int, forall c : int, forall d : int, (~ (n = (int_of_num (NUMERAL 0)))) -> ((a = b) /\ (~ (c = d))) -> ~ ((int_add a (int_mul n c)) = (int_add b (int_mul n d)))).
