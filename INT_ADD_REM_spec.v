Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2534337 : forall m : int, forall n : int, forall p : int, (rem (int_add (rem m p) (rem n p)) p) = (rem (int_add m n) p).
