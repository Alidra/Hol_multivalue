Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2317738 : forall P : int -> Prop, (forall n : nat, P (int_of_num n)) = (forall x : int, P (int_abs x)).
