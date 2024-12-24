Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3148697 : forall p : nat, (prime p) = (forall n : nat, (num_coprime (@pair nat nat p n)) = (~ (num_divides p n))).
