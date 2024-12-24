Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2838452 : forall a : nat, forall b : nat, (num_coprime (@pair nat nat a b)) = (int_coprime (@pair int int (int_of_num a) (int_of_num b))).
