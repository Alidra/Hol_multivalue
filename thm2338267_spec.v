Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2338267 : forall P : int -> Prop, (forall i : int, (int_le (int_of_num (NUMERAL 0)) i) -> P i) = (forall n : nat, P (int_of_num n)).