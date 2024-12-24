Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2535923 : forall m : int, forall n : int, forall p : int, (rem (int_sub (rem m p) (rem n p)) p) = (rem (int_sub m n) p).
