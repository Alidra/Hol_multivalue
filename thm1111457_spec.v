Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1111457 : forall {A : Type'}, (forall s : nat -> A, (@list_of_seq A s (NUMERAL 0)) = (@nil A)) /\ (forall s : nat -> A, forall n : nat, (@list_of_seq A s (S n)) = (@List.app A (@list_of_seq A s n) (@cons A (s n) (@nil A)))).
