Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2532785 : forall n : int, forall p : int, (rem (int_neg (rem n p)) p) = (rem (int_neg n) p).
