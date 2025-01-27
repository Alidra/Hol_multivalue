Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term18 := fun y0 : nat => NUMERAL (BIT1 0).
Definition term37 (a0 : Type') (x0 : a0) (x1 : list a0) := ~ ((@nil a0) = (@cons a0 x0 x1)).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a1) := (fun y0 : a1 => forall y1 : type1394 a0 a1, exists y2 : type1142 a0 a1, ((y2 (@nil a0)) = y0) /\ (forall y3 : a0, forall y4 : list a0, (y2 (@cons a0 y3 y4)) = (y1 y3 y4 (y2 y4)))) x0.
Definition term34 := @eq nat (NUMERAL 0).
Definition term25 (a0 : Type') (x0 : type1144 a0) := fun y0 : a0 => forall y1 : list a0, (x0 (@cons a0 y0 y1)) = ((fun y2 : a0 => fun y3 : list a0 => fun y4 : nat => NUMERAL (BIT1 0)) y0 y1 (x0 y1)).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1394 a0 a1) := (fun y0 : type1394 a0 a1 => exists y1 : type1142 a0 a1, ((y1 (@nil a0)) = x0) /\ (forall y2 : a0, forall y3 : list a0, (y1 (@cons a0 y2 y3)) = (y0 y2 y3 (y1 y3)))) x1.
Definition term26 (a0 : Type') (x0 : type1144 a0) := fun y0 : a0 => forall y1 : list a0, (x0 (@cons a0 y0 y1)) = (NUMERAL (BIT1 0)).
Definition term4 (a0 : Type') (x0 : type1144 a0) (x1 : a0) (x2 : list a0) := x0 (@cons a0 x1 x2).
Definition term1 (a0 : Type') (x0 : type1144 a0) (x1 : a0) := (fun y0 : a0 => forall y1 : list a0, (x0 (@cons a0 y0 y1)) = (NUMERAL (BIT1 0))) x1.
Definition term39 (a0 : Type') := forall y0 : a0, forall y1 : list a0, ~ ((@nil a0) = (@cons a0 y0 y1)).
Definition term23 (a0 : Type') (x0 : type1144 a0) (x1 : a0) := fun y0 : list a0 => (x0 (@cons a0 x1 y0)) = (NUMERAL (BIT1 0)).
Definition term32 (a0 : Type') := exists y0 : type1144 a0, ((y0 (@nil a0)) = (NUMERAL 0)) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = (NUMERAL (BIT1 0))).
Definition term12 (a0 : Type') := exists y0 : type1144 a0, ((y0 (@nil a0)) = (NUMERAL 0)) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = ((fun y3 : a0 => fun y4 : list a0 => fun y5 : nat => NUMERAL (BIT1 0)) y1 y2 (y0 y2))).
Definition term3 (a0 : Type') (x0 : type1144 a0) (x1 : a0) (x2 : list a0) := (fun y0 : list a0 => (x0 (@cons a0 x1 y0)) = (NUMERAL (BIT1 0))) x2.
Definition term36 (a0 : Type') (x0 : a0) (x1 : list a0) := ((@nil a0) = (@cons a0 x0 x1)) -> False.
Definition term24 (a0 : Type') (x0 : a0) (x1 : type1144 a0) := forall y0 : list a0, (x1 (@cons a0 x0 y0)) = ((fun y1 : a0 => fun y2 : list a0 => fun y3 : nat => NUMERAL (BIT1 0)) x0 y0 (x1 y0)).
Definition term22 (a0 : Type') (x0 : a0) (x1 : type1144 a0) := fun y0 : list a0 => (x1 (@cons a0 x0 y0)) = ((fun y1 : a0 => fun y2 : list a0 => fun y3 : nat => NUMERAL (BIT1 0)) x0 y0 (x1 y0)).
Definition term29 (a0 : Type') (x0 : type1144 a0) := ((x0 (@nil a0)) = (NUMERAL 0)) /\ (forall y0 : a0, forall y1 : list a0, (x0 (@cons a0 y0 y1)) = ((fun y2 : a0 => fun y3 : list a0 => fun y4 : nat => NUMERAL (BIT1 0)) y0 y1 (x0 y1))).
Definition term6 (a0 : Type') (x0 : type1144 a0) := ((x0 (@nil a0)) = (NUMERAL 0)) /\ (forall y0 : a0, forall y1 : list a0, (x0 (@cons a0 y0 y1)) = (NUMERAL (BIT1 0))).
Definition term16 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : a0 => fun y1 : list a0 => fun y2 : nat => NUMERAL (BIT1 0)) x0 x1.
Definition term14 (a0 : Type') (x0 : a0) := (fun y0 : a0 => fun y1 : list a0 => fun y2 : nat => NUMERAL (BIT1 0)) x0.
Definition term35 := S (Nat.add 0 0).
Definition term28 (a0 : Type') (x0 : type1144 a0) := and ((x0 (@nil a0)) = (NUMERAL 0)).
Definition term15 (a0 : Type') := fun y0 : list a0 => fun y1 : nat => NUMERAL (BIT1 0).
Definition term13 (a0 : Type') := fun y0 : a0 => fun y1 : list a0 => fun y2 : nat => NUMERAL (BIT1 0).
Definition term20 (a0 : Type') (x0 : type1144 a0) (x1 : list a0) := (fun y0 : nat => NUMERAL (BIT1 0)) (x0 x1).
Definition term38 (a0 : Type') (x0 : a0) := forall y0 : list a0, ~ ((@nil a0) = (@cons a0 x0 y0)).
Definition term33 (a0 : Type') (x0 : type1144 a0) := @eq nat (x0 (@nil a0)).
Definition term31 (a0 : Type') := fun y0 : type1144 a0 => ((y0 (@nil a0)) = (NUMERAL 0)) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = (NUMERAL (BIT1 0))).
Definition term30 (a0 : Type') := fun y0 : type1144 a0 => ((y0 (@nil a0)) = (NUMERAL 0)) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = ((fun y3 : a0 => fun y4 : list a0 => fun y5 : nat => NUMERAL (BIT1 0)) y1 y2 (y0 y2))).
Definition term2 (a0 : Type') (x0 : type1144 a0) (x1 : a0) := forall y0 : list a0, (x0 (@cons a0 x1 y0)) = (NUMERAL (BIT1 0)).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a1) := forall y0 : type1394 a0 a1, exists y1 : type1142 a0 a1, ((y1 (@nil a0)) = x0) /\ (forall y2 : a0, forall y3 : list a0, (y1 (@cons a0 y2 y3)) = (y0 y2 y3 (y1 y3))).
Definition term17 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => fun y1 : nat => NUMERAL (BIT1 0)) x0.
Definition term19 (a0 : Type') (x0 : a0) (x1 : type1144 a0) (x2 : list a0) := (fun y0 : a0 => fun y1 : list a0 => fun y2 : nat => NUMERAL (BIT1 0)) x0 x2 (x1 x2).
Definition term11 (a0 : Type') (x0 : nat) (x1 : type1396 a0) := exists y0 : type1144 a0, ((y0 (@nil a0)) = x0) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = (x1 y1 y2 (y0 y2))).
Definition term10 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1394 a0 a1) := exists y0 : type1142 a0 a1, ((y0 (@nil a0)) = x0) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = (x1 y1 y2 (y0 y2))).
Definition term27 (a0 : Type') (x0 : type1144 a0) := forall y0 : a0, forall y1 : list a0, (x0 (@cons a0 y0 y1)) = ((fun y2 : a0 => fun y3 : list a0 => fun y4 : nat => NUMERAL (BIT1 0)) y0 y1 (x0 y1)).
Definition term0 (a0 : Type') (x0 : type1144 a0) := forall y0 : a0, forall y1 : list a0, (x0 (@cons a0 y0 y1)) = (NUMERAL (BIT1 0)).
Definition term5 := NUMERAL (BIT1 0).
Definition term21 (a0 : Type') (x0 : type1144 a0) (x1 : a0) (x2 : list a0) := @eq nat (x0 (@cons a0 x1 x2)).
