Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2298395 : forall P : int -> Prop, (exists x : int, P x) = ((exists n : nat, P (int_of_num n)) \/ (exists n : nat, P (int_neg (int_of_num n)))).
