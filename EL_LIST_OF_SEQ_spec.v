Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1237532 : forall {A : Type'}, forall s : nat -> A, forall m : nat, forall n : nat, (Peano.lt m n) -> (@EL A m (@list_of_seq A s n)) = (s m).
