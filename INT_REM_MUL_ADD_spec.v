Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2661209 : (forall m : int, forall n : int, forall p : int, (rem (int_add (int_mul m n) p) n) = (rem p n)) /\ ((forall m : int, forall n : int, forall p : int, (rem (int_add (int_mul n m) p) n) = (rem p n)) /\ ((forall m : int, forall n : int, forall p : int, (rem (int_add p (int_mul m n)) n) = (rem p n)) /\ (forall m : int, forall n : int, forall p : int, (rem (int_add p (int_mul n m)) n) = (rem p n)))).
