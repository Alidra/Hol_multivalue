Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (a0 : Type') := fun y0 : list a0 => (y0 = (@nil a0)) = ((@List.length a0 y0) = (NUMERAL 0)).
Definition term11 := @eq nat (NUMERAL 0).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> (@List.length a0 (@list_of_set a0 x0)) = (@CARD a0 x0).
Definition term10 (a0 : Type') := @eq nat (@List.length a0 (@list_of_set a0 (@EMPTY a0))).
Definition term6 (a0 : Type') := forall y0 : list a0, (y0 = (@nil a0)) = ((@List.length a0 y0) = (NUMERAL 0)).
Definition term9 (a0 : Type') := (@FINITE a0 (@EMPTY a0)) -> (@List.length a0 (@list_of_set a0 (@EMPTY a0))) = (@CARD a0 (@EMPTY a0)).
Definition term8 (a0 : Type') := @List.length a0 (@list_of_set a0 (@EMPTY a0)).
Definition term5 (a0 : Type') := forall y0 : list a0, ((@List.length a0 y0) = (NUMERAL 0)) = (y0 = (@nil a0)).
Definition term3 (a0 : Type') := fun y0 : list a0 => ((@List.length a0 y0) = (NUMERAL 0)) = (y0 = (@nil a0)).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@List.length a0 (@list_of_set a0 y0)) = (@CARD a0 y0)) x0.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := @List.length a0 (@list_of_set a0 x0).
Definition term7 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => (y0 = (@nil a0)) = ((@List.length a0 y0) = (NUMERAL 0))) x0.
