Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') := fun y0 : list a0 => (y0 = (@nil a0)) = ((@List.length a0 y0) = (NUMERAL 0)).
Definition term11 (a0 : Type') (x0 : list a0) (x1 : list a0) := @List.length a0 (@List.app a0 x0 x1).
Definition term26 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term21 (a0 : Type') (x0 : list a0) (x1 : list a0) := (x0 = (@nil a0)) /\ (x1 = (@nil a0)).
Definition term3 (a0 : Type') := forall y0 : list a0, (y0 = (@nil a0)) = ((@List.length a0 y0) = (NUMERAL 0)).
Definition term29 (a0 : Type') := forall y0 : list a0, forall y1 : list a0, ((@List.app a0 y0 y1) = (@nil a0)) = ((y0 = (@nil a0)) /\ (y1 = (@nil a0))).
Definition term14 (a0 : Type') (x0 : list a0) (x1 : list a0) := @eq nat (@List.length a0 (@List.app a0 x0 x1)).
Definition term22 (a0 : Type') (x0 : list a0) := fun y0 : list a0 => ((@List.app a0 x0 y0) = (@nil a0)) = ((x0 = (@nil a0)) /\ (y0 = (@nil a0))).
Definition term8 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => forall y1 : list a0, (@List.length a0 (@List.app a0 y0 y1)) = (Nat.add (@List.length a0 y0) (@List.length a0 y1))) x0.
Definition term5 (x0 : nat) := forall y0 : nat, ((Nat.add x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0))).
Definition term7 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term25 (a0 : Type') := forall y0 : list a0, True.
Definition term19 (a0 : Type') (x0 : list a0) := and (x0 = (@nil a0)).
Definition term16 (a0 : Type') (x0 : list a0) (x1 : list a0) := ((@List.length a0 x0) = (NUMERAL 0)) /\ ((@List.length a0 x1) = (NUMERAL 0)).
Definition term24 (a0 : Type') (x0 : list a0) := forall y0 : list a0, ((@List.app a0 x0 y0) = (@nil a0)) = ((x0 = (@nil a0)) /\ (y0 = (@nil a0))).
Definition term2 (a0 : Type') := forall y0 : list a0, ((@List.length a0 y0) = (NUMERAL 0)) = (y0 = (@nil a0)).
Definition term0 (a0 : Type') := fun y0 : list a0 => ((@List.length a0 y0) = (NUMERAL 0)) = (y0 = (@nil a0)).
Definition term28 (a0 : Type') := fun y0 : list a0 => forall y1 : list a0, ((@List.app a0 y0 y1) = (@nil a0)) = ((y0 = (@nil a0)) /\ (y1 = (@nil a0))).
Definition term12 (a0 : Type') (x0 : list a0) (x1 : list a0) := Nat.add (@List.length a0 x0) (@List.length a0 x1).
Definition term17 (a0 : Type') (x0 : list a0) (x1 : list a0) := @eq Prop ((@List.app a0 x0 x1) = (@nil a0)).
Definition term18 (a0 : Type') (x0 : list a0) (x1 : list a0) := @eq Prop (((@List.length a0 x0) = (NUMERAL 0)) /\ ((@List.length a0 x1) = (NUMERAL 0))).
Definition term4 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) x0.
Definition term20 (a0 : Type') (x0 : list a0) := and ((@List.length a0 x0) = (NUMERAL 0)).
Definition term15 (a0 : Type') (x0 : list a0) (x1 : list a0) := @eq nat (Nat.add (@List.length a0 x0) (@List.length a0 x1)).
Definition term10 (a0 : Type') (x0 : list a0) (x1 : list a0) := (fun y0 : list a0 => (@List.length a0 (@List.app a0 x0 y0)) = (Nat.add (@List.length a0 x0) (@List.length a0 y0))) x1.
Definition term23 (a0 : Type') := fun y0 : list a0 => True.
Definition term9 (a0 : Type') (x0 : list a0) := forall y0 : list a0, (@List.length a0 (@List.app a0 x0 y0)) = (Nat.add (@List.length a0 x0) (@List.length a0 y0)).
Definition term27 (a0 : Type') (x0 : Prop) := forall y0 : list a0, x0.
Definition term13 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => (y0 = (@nil a0)) = ((@List.length a0 y0) = (NUMERAL 0))) x0.
Definition term6 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.add x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) x1.
