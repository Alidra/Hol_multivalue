Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2530606 : (forall m : int, forall n : int, forall p : int, (rem (rem m (int_mul n p)) n) = (rem m n)) /\ (forall m : int, forall n : int, forall p : int, (rem (rem m (int_mul n p)) p) = (rem m p)).