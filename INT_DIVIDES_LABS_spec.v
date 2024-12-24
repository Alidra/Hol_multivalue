Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2804399 : forall d : int, forall n : int, (int_divides (int_abs d) n) = (int_divides d n).
