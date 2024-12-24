Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1066562 : forall {A : Type'} (a : A) (f : nat -> A) (n : nat), ((fun n' : nat => (@FCONS A a f (S n')) = (f n')) n) = ((@FCONS A a f (S n)) = (f n)).
