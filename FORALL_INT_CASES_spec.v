Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2296993 : forall P : int -> Prop, (forall x : int, P x) = ((forall n : nat, P (int_of_num n)) /\ (forall n : nat, P (int_neg (int_of_num n)))).
