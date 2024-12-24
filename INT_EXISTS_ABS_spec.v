Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2317958 : forall P : int -> Prop, (exists n : nat, P (int_of_num n)) = (exists x : int, P (int_abs x)).
