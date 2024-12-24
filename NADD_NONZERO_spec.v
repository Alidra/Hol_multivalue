Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1299985 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL 0)))) -> exists N : nat, forall n : nat, (Peano.le N n) -> ~ ((dest_nadd x n) = (NUMERAL 0)).
