Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1237614 : forall {A : Type'}, forall s : nat -> A, forall n : nat, ((@list_of_seq A s n) = (@nil A)) = (n = (NUMERAL 0)).
