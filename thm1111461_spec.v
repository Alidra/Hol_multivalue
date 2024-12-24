Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1111461 : forall {A : Type'} (s : nat -> A), ((fun s' : nat -> A => (@list_of_seq A s' (NUMERAL 0)) = (@nil A)) s) = ((@list_of_seq A s (NUMERAL 0)) = (@nil A)).
