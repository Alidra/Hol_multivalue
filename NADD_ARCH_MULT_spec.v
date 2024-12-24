Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1286557 : forall x : nadd, forall k : nat, (~ (nadd_eq x (nadd_of_num (NUMERAL 0)))) -> exists N : nat, nadd_le (nadd_of_num k) (nadd_mul (nadd_of_num N) x).
