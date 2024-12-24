Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term30 := @eq nat (NUMERAL 0).
Definition term39 (a0 : Type') (x0 : a0) (x1 : list a0) := @List.length a0 (@cons a0 x0 x1).
Definition term50 (a0 : Type') (x0 : nat) := fun y0 : a0 => (@List.length a0 (@repeat_with_perm_args a0 (S x0) y0)) = (S x0).
Definition term34 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term18 (a0 : Type') := forall y0 : nat, (forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) -> forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 (S y0) y1)) = (S y0).
Definition term37 (a0 : Type') (x0 : a0) := forall y0 : list a0, (@List.length a0 (@cons a0 x0 y0)) = (S (@List.length a0 y0)).
Definition term26 (a0 : Type') := ((forall y0 : a0, (@List.length a0 (@repeat_with_perm_args a0 (NUMERAL 0) y0)) = (NUMERAL 0)) /\ (forall y0 : nat, (forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) -> forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 (S y0) y1)) = (S y0))) -> forall y0 : nat, forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0.
Definition term33 (a0 : Type') := forall y0 : a0, True.
Definition term40 (a0 : Type') (x0 : list a0) := S (@List.length a0 x0).
Definition term20 (a0 : Type') := (forall y0 : a0, (@List.length a0 (@repeat_with_perm_args a0 (NUMERAL 0) y0)) = (NUMERAL 0)) /\ (forall y0 : nat, (forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) -> forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 (S y0) y1)) = (S y0)).
Definition term9 (a0 : Type') (x0 : nat) := imp ((fun y0 : nat => forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) x0).
Definition term16 (a0 : Type') := fun y0 : nat => (forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) -> forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 (S y0) y1)) = (S y0).
Definition term1 (a0 : Type') := (((fun y0 : nat => forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : a0, (@List.length a0 (@repeat_with_perm_args a0 y1 y2)) = y1) y0) -> (fun y1 : nat => forall y2 : a0, (@List.length a0 (@repeat_with_perm_args a0 y1 y2)) = y1) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : a0, (@List.length a0 (@repeat_with_perm_args a0 y1 y2)) = y1) y0.
Definition term6 (a0 : Type') := and (forall y0 : a0, (@List.length a0 (@repeat_with_perm_args a0 (NUMERAL 0) y0)) = (NUMERAL 0)).
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term21 (a0 : Type') := imp (((fun y0 : nat => forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : a0, (@List.length a0 (@repeat_with_perm_args a0 y1 y2)) = y1) y0) -> (fun y1 : nat => forall y2 : a0, (@List.length a0 (@repeat_with_perm_args a0 y1 y2)) = y1) (S y0))).
Definition term29 (a0 : Type') (x0 : a0) := @eq nat (@List.length a0 (@repeat_with_perm_args a0 (NUMERAL 0) x0)).
Definition term17 (a0 : Type') := forall y0 : nat, ((fun y1 : nat => forall y2 : a0, (@List.length a0 (@repeat_with_perm_args a0 y1 y2)) = y1) y0) -> (fun y1 : nat => forall y2 : a0, (@List.length a0 (@repeat_with_perm_args a0 y1 y2)) = y1) (S y0).
Definition term28 (a0 : Type') (x0 : a0) := @List.length a0 (@repeat_with_perm_args a0 (NUMERAL 0) x0).
Definition term10 (a0 : Type') (x0 : nat) := imp (forall y0 : a0, (@List.length a0 (@repeat_with_perm_args a0 x0 y0)) = x0).
Definition term2 (a0 : Type') := fun y0 : nat => forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0.
Definition term43 (a0 : Type') (x0 : nat) (x1 : a0) := @repeat_with_perm_args a0 (S x0) x1.
Definition term31 (a0 : Type') := fun y0 : a0 => (@List.length a0 (@repeat_with_perm_args a0 (NUMERAL 0) y0)) = (NUMERAL 0).
Definition term5 (a0 : Type') := and ((fun y0 : nat => forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) (NUMERAL 0)).
Definition term11 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) (S x0).
Definition term47 (a0 : Type') (x0 : nat) (x1 : a0) := S (@List.length a0 (@repeat_with_perm_args a0 x0 x1)).
Definition term3 (a0 : Type') := (fun y0 : nat => forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) (NUMERAL 0).
Definition term22 (a0 : Type') := imp ((forall y0 : a0, (@List.length a0 (@repeat_with_perm_args a0 (NUMERAL 0) y0)) = (NUMERAL 0)) /\ (forall y0 : nat, (forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) -> forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 (S y0) y1)) = (S y0))).
Definition term36 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : list a0, (@List.length a0 (@cons a0 y0 y1)) = (S (@List.length a0 y1))) x0.
Definition term25 (a0 : Type') := forall y0 : nat, forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0.
Definition term32 (a0 : Type') := fun y0 : a0 => True.
Definition term27 (a0 : Type') (x0 : a0) := @repeat_with_perm_args a0 (NUMERAL 0) x0.
Definition term14 (a0 : Type') (x0 : nat) := (forall y0 : a0, (@List.length a0 (@repeat_with_perm_args a0 x0 y0)) = x0) -> forall y0 : a0, (@List.length a0 (@repeat_with_perm_args a0 (S x0) y0)) = (S x0).
Definition term38 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => (@List.length a0 (@cons a0 x0 y0)) = (S (@List.length a0 y0))) x1.
Definition term4 (a0 : Type') := forall y0 : a0, (@List.length a0 (@repeat_with_perm_args a0 (NUMERAL 0) y0)) = (NUMERAL 0).
Definition term15 (a0 : Type') := fun y0 : nat => ((fun y1 : nat => forall y2 : a0, (@List.length a0 (@repeat_with_perm_args a0 y1 y2)) = y1) y0) -> (fun y1 : nat => forall y2 : a0, (@List.length a0 (@repeat_with_perm_args a0 y1 y2)) = y1) (S y0).
Definition term42 (a0 : Type') (x0 : nat) (x1 : a0) := @List.length a0 (@repeat_with_perm_args a0 x0 x1).
Definition term7 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) x0.
Definition term49 (x0 : nat) := @eq nat (S x0).
Definition term44 (a0 : Type') (x0 : nat) (x1 : a0) := @cons a0 x1 (@repeat_with_perm_args a0 x0 x1).
Definition term45 (a0 : Type') (x0 : nat) (x1 : a0) := @List.length a0 (@repeat_with_perm_args a0 (S x0) x1).
Definition term23 (a0 : Type') := fun y0 : nat => (fun y1 : nat => forall y2 : a0, (@List.length a0 (@repeat_with_perm_args a0 y1 y2)) = y1) y0.
Definition term41 (a0 : Type') (x0 : nat) (x1 : a0) := (fun y0 : a0 => (@List.length a0 (@repeat_with_perm_args a0 x0 y0)) = x0) x1.
Definition term19 (a0 : Type') := ((fun y0 : nat => forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : a0, (@List.length a0 (@repeat_with_perm_args a0 y1 y2)) = y1) y0) -> (fun y1 : nat => forall y2 : a0, (@List.length a0 (@repeat_with_perm_args a0 y1 y2)) = y1) (S y0)).
Definition term48 (a0 : Type') (x0 : nat) (x1 : a0) := @eq nat (@List.length a0 (@repeat_with_perm_args a0 (S x0) x1)).
Definition term8 (a0 : Type') (x0 : nat) := forall y0 : a0, (@List.length a0 (@repeat_with_perm_args a0 x0 y0)) = x0.
Definition term12 (a0 : Type') (x0 : nat) := forall y0 : a0, (@List.length a0 (@repeat_with_perm_args a0 (S x0) y0)) = (S x0).
Definition term13 (a0 : Type') (x0 : nat) := ((fun y0 : nat => forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) x0) -> (fun y0 : nat => forall y1 : a0, (@List.length a0 (@repeat_with_perm_args a0 y0 y1)) = y0) (S x0).
Definition term24 (a0 : Type') := forall y0 : nat, (fun y1 : nat => forall y2 : a0, (@List.length a0 (@repeat_with_perm_args a0 y1 y2)) = y1) y0.
Definition term35 (a0 : Type') := forall y0 : a0, forall y1 : list a0, (@List.length a0 (@cons a0 y0 y1)) = (S (@List.length a0 y1)).
Definition term46 (a0 : Type') (x0 : nat) (x1 : a0) := @List.length a0 (@cons a0 x1 (@repeat_with_perm_args a0 x0 x1)).
