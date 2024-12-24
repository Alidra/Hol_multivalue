Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2528731 : forall (n : int) (m : int) (p : int), (@eq2 int (rem m (int_mul n p)) m (int_mod p)) = ((rem (rem m (int_mul n p)) p) = (rem m p)).
