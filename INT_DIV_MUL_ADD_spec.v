Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2704369 : (forall m : int, forall n : int, forall p : int, (~ (n = (int_of_num (NUMERAL 0)))) -> (div (int_add (int_mul m n) p) n) = (int_add m (div p n))) /\ ((forall m : int, forall n : int, forall p : int, (~ (n = (int_of_num (NUMERAL 0)))) -> (div (int_add (int_mul n m) p) n) = (int_add m (div p n))) /\ ((forall m : int, forall n : int, forall p : int, (~ (n = (int_of_num (NUMERAL 0)))) -> (div (int_add p (int_mul m n)) n) = (int_add (div p n) m)) /\ (forall m : int, forall n : int, forall p : int, (~ (n = (int_of_num (NUMERAL 0)))) -> (div (int_add p (int_mul n m)) n) = (int_add (div p n) m)))).
