Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2537472 : forall m : int, forall n : int, forall p : int, (rem (int_mul (rem m p) (rem n p)) p) = (rem (int_mul m n) p).
