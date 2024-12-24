Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') := fun y0 : list a0 => (y0 = (@nil a0)) = ((@List.length a0 y0) = (NUMERAL 0)).
Definition term16 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term18 (a0 : Type') := fun y0 : nat -> a0 => forall y1 : nat, ((@list_of_seq a0 y0 y1) = (@nil a0)) = (y1 = (NUMERAL 0)).
Definition term3 (a0 : Type') := forall y0 : list a0, (y0 = (@nil a0)) = ((@List.length a0 y0) = (NUMERAL 0)).
Definition term9 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := @eq nat (@List.length a0 (@list_of_seq a0 x0 x1)).
Definition term7 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := @List.length a0 (@list_of_seq a0 x0 x1).
Definition term14 (a0 : Type') (x0 : nat -> a0) := forall y0 : nat, ((@list_of_seq a0 x0 y0) = (@nil a0)) = (y0 = (NUMERAL 0)).
Definition term2 (a0 : Type') := forall y0 : list a0, ((@List.length a0 y0) = (NUMERAL 0)) = (y0 = (@nil a0)).
Definition term21 (a0 : Type') := forall y0 : nat -> a0, True.
Definition term0 (a0 : Type') := fun y0 : list a0 => ((@List.length a0 y0) = (NUMERAL 0)) = (y0 = (@nil a0)).
Definition term15 := forall y0 : nat, True.
Definition term4 (a0 : Type') (x0 : nat -> a0) := (fun y0 : nat -> a0 => forall y1 : nat, (@List.length a0 (@list_of_seq a0 y0 y1)) = y1) x0.
Definition term13 := fun y0 : nat => True.
Definition term10 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := @eq Prop ((@list_of_seq a0 x0 x1) = (@nil a0)).
Definition term19 (a0 : Type') := fun y0 : nat -> a0 => True.
Definition term5 (a0 : Type') (x0 : nat -> a0) := forall y0 : nat, (@List.length a0 (@list_of_seq a0 x0 y0)) = y0.
Definition term20 (a0 : Type') := forall y0 : nat -> a0, forall y1 : nat, ((@list_of_seq a0 y0 y1) = (@nil a0)) = (y1 = (NUMERAL 0)).
Definition term22 (a0 : Type') (x0 : Prop) := forall y0 : nat -> a0, x0.
Definition term12 (a0 : Type') (x0 : nat -> a0) := fun y0 : nat => ((@list_of_seq a0 x0 y0) = (@nil a0)) = (y0 = (NUMERAL 0)).
Definition term6 (a0 : Type') (x0 : nat -> a0) (x1 : nat) := (fun y0 : nat => (@List.length a0 (@list_of_seq a0 x0 y0)) = y0) x1.
Definition term17 (x0 : Prop) := forall y0 : nat, x0.
Definition term8 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => (y0 = (@nil a0)) = ((@List.length a0 y0) = (NUMERAL 0))) x0.
Definition term11 (x0 : nat) := @eq Prop (x0 = (NUMERAL 0)).
