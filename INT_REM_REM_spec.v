Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2521244 : forall m : int, forall n : int, (rem (rem m n) n) = (rem m n).
