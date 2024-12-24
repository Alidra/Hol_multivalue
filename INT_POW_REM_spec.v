Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2537700 : forall m : int, forall n : nat, forall p : int, (rem (int_pow (rem m p) n) p) = (rem (int_pow m n) p).
