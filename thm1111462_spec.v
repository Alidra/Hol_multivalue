Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1111462 : forall {A : Type'} (s : nat -> A), (@list_of_seq A s (NUMERAL 0)) = (@nil A).