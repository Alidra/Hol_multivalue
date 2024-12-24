Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2338993 : forall (P : int -> Prop), ((~ (forall x : int, (int_le (int_of_num (NUMERAL 0)) x) -> ~ (P x))) = (~ (forall x : int, (int_le (int_of_num (NUMERAL 0)) x) -> ~ ((P x) /\ (forall y : int, ((int_le (int_of_num (NUMERAL 0)) y) /\ (P y)) -> int_le x y))))) = ((exists x : int, (int_le (int_of_num (NUMERAL 0)) x) /\ (P x)) = (exists x : int, (int_le (int_of_num (NUMERAL 0)) x) /\ ((P x) /\ (forall y : int, ((int_le (int_of_num (NUMERAL 0)) y) /\ (P y)) -> int_le x y)))).
