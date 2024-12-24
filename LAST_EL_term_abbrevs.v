Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term106 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : Prop) (x3 : a0) (x4 : a0) := (fun y0 : a0 => (((@List.length a0 x1) = (NUMERAL 0)) = x2) -> (x2 -> x0 = x3) -> ((~ x2) -> (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1) = y0) -> (@COND a0 ((@List.length a0 x1) = (NUMERAL 0)) x0 (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1)) = (@COND a0 x2 x3 y0)) x4.
Definition term21 (a0 : Type') (x0 : a0) (x1 : list a0) := ((fun y0 : list a0 => (~ (y0 = (@nil a0))) -> (@LAST a0 y0) = (@EL a0 (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0))) y0)) x1) -> (fun y0 : list a0 => (~ (y0 = (@nil a0))) -> (@LAST a0 y0) = (@EL a0 (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0))) y0)) (@cons a0 x0 x1).
Definition term126 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : a0) := ((~ False) -> (@EL a0 (Nat.sub (@List.length a0 x0) (NUMERAL (BIT1 0))) x0) = x2) -> (@COND a0 ((@List.length a0 x0) = (NUMERAL 0)) x1 (@EL a0 (Nat.sub (@List.length a0 x0) (NUMERAL (BIT1 0))) x0)) = (@COND a0 False x1 x2).
Definition term112 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : a0) := ((~ True) -> (@EL a0 (Nat.sub (@List.length a0 x0) (NUMERAL (BIT1 0))) x0) = x2) -> (@COND a0 ((@List.length a0 x0) = (NUMERAL 0)) x1 (@EL a0 (Nat.sub (@List.length a0 x0) (NUMERAL (BIT1 0))) x0)) = (@COND a0 True x1 x2).
Definition term39 (a0 : Type') := ~ ((@nil a0) = (@nil a0)).
Definition term53 (a0 : Type') (x0 : a0) (x1 : list a0) := @COND a0 (x1 = (@nil a0)) x0 (@LAST a0 x1).
Definition term121 (a0 : Type') (x0 : list a0) := @eq a0 (@EL a0 (Nat.sub (@List.length a0 x0) (NUMERAL (BIT1 0))) x0).
Definition term28 (a0 : Type') := fun y0 : a0 => forall y1 : list a0, ((~ (y1 = (@nil a0))) -> (@LAST a0 y1) = (@EL a0 (Nat.sub (@List.length a0 y1) (NUMERAL (BIT1 0))) y1)) -> (~ ((@cons a0 y0 y1) = (@nil a0))) -> (@LAST a0 (@cons a0 y0 y1)) = (@EL a0 (Nat.sub (@List.length a0 (@cons a0 y0 y1)) (NUMERAL (BIT1 0))) (@cons a0 y0 y1)).
Definition term59 (a0 : Type') (x0 : list a0) := Nat.sub (S (@List.length a0 x0)) (NUMERAL (BIT1 0)).
Definition term6 (a0 : Type') (x0 : a0) (x1 : list a0) := @List.length a0 (@cons a0 x0 x1).
Definition term33 (a0 : Type') := imp (((fun y0 : list a0 => (~ (y0 = (@nil a0))) -> (@LAST a0 y0) = (@EL a0 (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0))) y0)) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => (~ (y2 = (@nil a0))) -> (@LAST a0 y2) = (@EL a0 (Nat.sub (@List.length a0 y2) (NUMERAL (BIT1 0))) y2)) y1) -> (fun y2 : list a0 => (~ (y2 = (@nil a0))) -> (@LAST a0 y2) = (@EL a0 (Nat.sub (@List.length a0 y2) (NUMERAL (BIT1 0))) y2)) (@cons a0 y0 y1))).
Definition term129 (a0 : Type') (x0 : a0) (x1 : list a0) := @COND a0 False x0 (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1).
Definition term119 (a0 : Type') (x0 : list a0) := (~ (x0 = (@nil a0))) -> (x0 = (@nil a0)) = False.
Definition term109 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : a0) := (True -> x0 = x2) -> ((~ True) -> (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1) = x3) -> (@COND a0 ((@List.length a0 x1) = (NUMERAL 0)) x0 (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1)) = (@COND a0 True x2 x3).
Definition term37 (a0 : Type') := forall y0 : list a0, (~ (y0 = (@nil a0))) -> (@LAST a0 y0) = (@EL a0 (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0))) y0).
Definition term9 (a0 : Type') := (((fun y0 : list a0 => (~ (y0 = (@nil a0))) -> (@LAST a0 y0) = (@EL a0 (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0))) y0)) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => (~ (y2 = (@nil a0))) -> (@LAST a0 y2) = (@EL a0 (Nat.sub (@List.length a0 y2) (NUMERAL (BIT1 0))) y2)) y1) -> (fun y2 : list a0 => (~ (y2 = (@nil a0))) -> (@LAST a0 y2) = (@EL a0 (Nat.sub (@List.length a0 y2) (NUMERAL (BIT1 0))) y2)) (@cons a0 y0 y1))) -> forall y0 : list a0, (fun y1 : list a0 => (~ (y1 = (@nil a0))) -> (@LAST a0 y1) = (@EL a0 (Nat.sub (@List.length a0 y1) (NUMERAL (BIT1 0))) y1)) y0.
Definition term63 (a0 : Type') (x0 : a0) (x1 : list a0) := @EL a0 (@List.length a0 x1) (@cons a0 x0 x1).
Definition term8 (a0 : Type') (x0 : type1143 a0) := ((x0 (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, (x0 y1) -> x0 (@cons a0 y0 y1))) -> forall y0 : list a0, x0 y0.
Definition term75 (a0 : Type') (x0 : a0) (x1 : list a0) := (~ (x1 = (@nil a0))) -> (fun y0 : a0 => y0 = (@EL a0 (@List.length a0 x1) (@cons a0 x0 x1))) (@LAST a0 x1).
Definition term4 (a0 : Type') (x0 : a0) := forall y0 : list a0, (@List.length a0 (@cons a0 x0 y0)) = (S (@List.length a0 y0)).
Definition term23 (a0 : Type') (x0 : a0) := fun y0 : list a0 => ((fun y1 : list a0 => (~ (y1 = (@nil a0))) -> (@LAST a0 y1) = (@EL a0 (Nat.sub (@List.length a0 y1) (NUMERAL (BIT1 0))) y1)) y0) -> (fun y1 : list a0 => (~ (y1 = (@nil a0))) -> (@LAST a0 y1) = (@EL a0 (Nat.sub (@List.length a0 y1) (NUMERAL (BIT1 0))) y1)) (@cons a0 x0 y0).
Definition term7 (a0 : Type') (x0 : list a0) := S (@List.length a0 x0).
Definition term105 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : Prop) (x3 : a0) := forall y0 : a0, (((@List.length a0 x1) = (NUMERAL 0)) = x2) -> (x2 -> x0 = x3) -> ((~ x2) -> (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1) = y0) -> (@COND a0 ((@List.length a0 x1) = (NUMERAL 0)) x0 (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1)) = (@COND a0 x2 x3 y0).
Definition term97 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) := forall y0 : a0, (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = y0) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 y0).
Definition term95 (a0 : Type') (x0 : a0) (x1 : list a0) := @COND a0 ((@List.length a0 x1) = (NUMERAL 0)) x0 (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1).
Definition term11 (a0 : Type') := (fun y0 : list a0 => (~ (y0 = (@nil a0))) -> (@LAST a0 y0) = (@EL a0 (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0))) y0)) (@nil a0).
Definition term12 (a0 : Type') := (~ ((@nil a0) = (@nil a0))) -> (@LAST a0 (@nil a0)) = (@EL a0 (Nat.sub (@List.length a0 (@nil a0)) (NUMERAL (BIT1 0))) (@nil a0)).
Definition term87 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => ((@List.length a0 y0) = (NUMERAL 0)) = (y0 = (@nil a0))) x0.
Definition term76 (a0 : Type') (x0 : a0) (x1 : list a0) := (~ (x1 = (@nil a0))) -> (@LAST a0 x1) = (@EL a0 (@List.length a0 x1) (@cons a0 x0 x1)).
Definition term91 (a0 : Type') (x0 : a0) (x1 : nat) := forall y0 : list a0, (@EL a0 x1 (@cons a0 x0 y0)) = (@COND a0 (x1 = (NUMERAL 0)) x0 (@EL a0 (Nat.sub x1 (NUMERAL (BIT1 0))) y0)).
Definition term0 (x0 : nat) := (fun y0 : nat => (Nat.sub (S y0) (NUMERAL (BIT1 0))) = y0) x0.
Definition term35 (a0 : Type') := fun y0 : list a0 => (fun y1 : list a0 => (~ (y1 = (@nil a0))) -> (@LAST a0 y1) = (@EL a0 (Nat.sub (@List.length a0 y1) (NUMERAL (BIT1 0))) y1)) y0.
Definition term90 (a0 : Type') (x0 : nat) (x1 : a0) := (fun y0 : a0 => forall y1 : list a0, (@EL a0 x0 (@cons a0 y0 y1)) = (@COND a0 (x0 = (NUMERAL 0)) y0 (@EL a0 (Nat.sub x0 (NUMERAL (BIT1 0))) y1))) x1.
Definition term108 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : a0) := (((@List.length a0 x1) = (NUMERAL 0)) = True) -> (True -> x0 = x2) -> ((~ True) -> (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1) = x3) -> (@COND a0 ((@List.length a0 x1) = (NUMERAL 0)) x0 (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1)) = (@COND a0 True x2 x3).
Definition term113 (a0 : Type') (x0 : list a0) := Nat.sub (@List.length a0 x0).
Definition term41 (a0 : Type') := Nat.sub (@List.length a0 (@nil a0)).
Definition term88 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0, forall y2 : list a0, (@EL a0 y0 (@cons a0 y1 y2)) = (@COND a0 (y0 = (NUMERAL 0)) y1 (@EL a0 (Nat.sub y0 (NUMERAL (BIT1 0))) y2))) x0.
Definition term51 (a0 : Type') := False -> (@LAST a0 (@nil a0)) = (@EL a0 (Nat.sub (NUMERAL 0) (NUMERAL (BIT1 0))) (@nil a0)).
Definition term65 (a0 : Type') (x0 : a0) (x1 : list a0) := (~ ((@cons a0 x0 x1) = (@nil a0))) -> (@COND a0 (x1 = (@nil a0)) x0 (@LAST a0 x1)) = (@EL a0 (@List.length a0 x1) (@cons a0 x0 x1)).
Definition term27 (a0 : Type') := fun y0 : a0 => forall y1 : list a0, ((fun y2 : list a0 => (~ (y2 = (@nil a0))) -> (@LAST a0 y2) = (@EL a0 (Nat.sub (@List.length a0 y2) (NUMERAL (BIT1 0))) y2)) y1) -> (fun y2 : list a0 => (~ (y2 = (@nil a0))) -> (@LAST a0 y2) = (@EL a0 (Nat.sub (@List.length a0 y2) (NUMERAL (BIT1 0))) y2)) (@cons a0 y0 y1).
Definition term55 (a0 : Type') (x0 : a0) (x1 : list a0) := @eq a0 (@COND a0 (x1 = (@nil a0)) x0 (@LAST a0 x1)).
Definition term1 (x0 : nat) := Nat.sub (S x0) (NUMERAL (BIT1 0)).
Definition term68 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : Prop) (x3 : a0) (x4 : a0) := (fun y0 : a0 => y0 = (@EL a0 (@List.length a0 x1) (@cons a0 x0 x1))) (@COND a0 x2 x3 x4).
Definition term52 (a0 : Type') (x0 : a0) (x1 : list a0) := @LAST a0 (@cons a0 x0 x1).
Definition term80 (a0 : Type') (x0 : a0) (x1 : list a0) := (x1 = (@nil a0)) -> x0 = (@EL a0 (@List.length a0 x1) (@cons a0 x0 x1)).
Definition term58 (a0 : Type') (x0 : a0) (x1 : list a0) := Nat.sub (@List.length a0 (@cons a0 x0 x1)) (NUMERAL (BIT1 0)).
Definition term128 (a0 : Type') (x0 : a0) (x1 : list a0) := ((~ False) -> (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1) = (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1)) -> (@COND a0 ((@List.length a0 x1) = (NUMERAL 0)) x0 (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1)) = (@COND a0 False x0 (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1)).
Definition term49 (a0 : Type') := @EL a0 (Nat.sub (NUMERAL 0) (NUMERAL (BIT1 0))) (@nil a0).
Definition term48 (a0 : Type') := @EL a0 (Nat.sub (@List.length a0 (@nil a0)) (NUMERAL (BIT1 0))) (@nil a0).
Definition term16 (a0 : Type') (x0 : list a0) := (~ (x0 = (@nil a0))) -> (@LAST a0 x0) = (@EL a0 (Nat.sub (@List.length a0 x0) (NUMERAL (BIT1 0))) x0).
Definition term118 (a0 : Type') (x0 : a0) := @COND a0 True x0 (@EL a0 (Nat.sub (NUMERAL 0) (NUMERAL (BIT1 0))) (@nil a0)).
Definition term70 (a0 : Type') (x0 : a0) (x1 : list a0) := fun y0 : a0 => y0 = (@EL a0 (@List.length a0 x1) (@cons a0 x0 x1)).
Definition term45 := Nat.sub (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term79 (a0 : Type') (x0 : list a0) (x1 : a0) := (x0 = (@nil a0)) -> (fun y0 : a0 => y0 = (@EL a0 (@List.length a0 x0) (@cons a0 x1 x0))) x1.
Definition term104 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : Prop) (x3 : a0) := (fun y0 : a0 => forall y1 : a0, (((@List.length a0 x1) = (NUMERAL 0)) = x2) -> (x2 -> x0 = y0) -> ((~ x2) -> (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1) = y1) -> (@COND a0 ((@List.length a0 x1) = (NUMERAL 0)) x0 (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1)) = (@COND a0 x2 y0 y1)) x3.
Definition term81 (a0 : Type') (x0 : list a0) (x1 : a0) := and ((x0 = (@nil a0)) -> (fun y0 : a0 => y0 = (@EL a0 (@List.length a0 x0) (@cons a0 x1 x0))) x1).
Definition term62 (a0 : Type') (x0 : a0) (x1 : list a0) := @EL a0 (Nat.sub (@List.length a0 (@cons a0 x0 x1)) (NUMERAL (BIT1 0))) (@cons a0 x0 x1).
Definition term67 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : a0 -> Prop) (x3 : a0) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term124 (a0 : Type') (x0 : a0) := False -> x0 = x0.
Definition term116 (a0 : Type') (x0 : list a0) := (~ True) -> (@EL a0 (Nat.sub (@List.length a0 x0) (NUMERAL (BIT1 0))) x0) = (@EL a0 (Nat.sub (NUMERAL 0) (NUMERAL (BIT1 0))) (@nil a0)).
Definition term18 (a0 : Type') (x0 : list a0) := imp ((~ (x0 = (@nil a0))) -> (@LAST a0 x0) = (@EL a0 (Nat.sub (@List.length a0 x0) (NUMERAL (BIT1 0))) x0)).
Definition term19 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => (~ (y0 = (@nil a0))) -> (@LAST a0 y0) = (@EL a0 (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0))) y0)) (@cons a0 x0 x1).
Definition term117 (a0 : Type') (x0 : list a0) (x1 : a0) := ((~ True) -> (@EL a0 (Nat.sub (@List.length a0 x0) (NUMERAL (BIT1 0))) x0) = (@EL a0 (Nat.sub (NUMERAL 0) (NUMERAL (BIT1 0))) (@nil a0))) -> (@COND a0 ((@List.length a0 x0) = (NUMERAL 0)) x1 (@EL a0 (Nat.sub (@List.length a0 x0) (NUMERAL (BIT1 0))) x0)) = (@COND a0 True x1 (@EL a0 (Nat.sub (NUMERAL 0) (NUMERAL (BIT1 0))) (@nil a0))).
Definition term71 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : a0 => y0 = (@EL a0 (@List.length a0 x1) (@cons a0 x0 x1))) (@COND a0 (x1 = (@nil a0)) x0 (@LAST a0 x1)).
Definition term111 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : a0) := (True -> x1 = x1) -> ((~ True) -> (@EL a0 (Nat.sub (@List.length a0 x0) (NUMERAL (BIT1 0))) x0) = x2) -> (@COND a0 ((@List.length a0 x0) = (NUMERAL 0)) x1 (@EL a0 (Nat.sub (@List.length a0 x0) (NUMERAL (BIT1 0))) x0)) = (@COND a0 True x1 x2).
Definition term102 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : Prop) := (fun y0 : Prop => forall y1 : a0, forall y2 : a0, (((@List.length a0 x1) = (NUMERAL 0)) = y0) -> (y0 -> x0 = y1) -> ((~ y0) -> (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1) = y2) -> (@COND a0 ((@List.length a0 x1) = (NUMERAL 0)) x0 (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1)) = (@COND a0 y0 y1 y2)) x2.
Definition term77 (a0 : Type') (x0 : list a0) (x1 : a0) := (fun y0 : a0 => y0 = (@EL a0 (@List.length a0 x0) (@cons a0 x1 x0))) x1.
Definition term78 (a0 : Type') (x0 : list a0) := imp (x0 = (@nil a0)).
Definition term24 (a0 : Type') (x0 : a0) := fun y0 : list a0 => ((~ (y0 = (@nil a0))) -> (@LAST a0 y0) = (@EL a0 (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0))) y0)) -> (~ ((@cons a0 x0 y0) = (@nil a0))) -> (@LAST a0 (@cons a0 x0 y0)) = (@EL a0 (Nat.sub (@List.length a0 (@cons a0 x0 y0)) (NUMERAL (BIT1 0))) (@cons a0 x0 y0)).
Definition term25 (a0 : Type') (x0 : a0) := forall y0 : list a0, ((fun y1 : list a0 => (~ (y1 = (@nil a0))) -> (@LAST a0 y1) = (@EL a0 (Nat.sub (@List.length a0 y1) (NUMERAL (BIT1 0))) y1)) y0) -> (fun y1 : list a0 => (~ (y1 = (@nil a0))) -> (@LAST a0 y1) = (@EL a0 (Nat.sub (@List.length a0 y1) (NUMERAL (BIT1 0))) y1)) (@cons a0 x0 y0).
Definition term3 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : list a0, (@List.length a0 (@cons a0 y0 y1)) = (S (@List.length a0 y1))) x0.
Definition term84 (a0 : Type') (x0 : a0) (x1 : list a0) := @eq Prop ((fun y0 : a0 => y0 = (@EL a0 (@List.length a0 x1) (@cons a0 x0 x1))) (@COND a0 (x1 = (@nil a0)) x0 (@LAST a0 x1))).
Definition term85 (a0 : Type') (x0 : a0) (x1 : list a0) := @eq Prop ((@COND a0 (x1 = (@nil a0)) x0 (@LAST a0 x1)) = (@EL a0 (@List.length a0 x1) (@cons a0 x0 x1))).
Definition term13 (a0 : Type') := and ((fun y0 : list a0 => (~ (y0 = (@nil a0))) -> (@LAST a0 y0) = (@EL a0 (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0))) y0)) (@nil a0)).
Definition term60 (a0 : Type') (x0 : a0) (x1 : list a0) := @EL a0 (Nat.sub (@List.length a0 (@cons a0 x0 x1)) (NUMERAL (BIT1 0))).
Definition term26 (a0 : Type') (x0 : a0) := forall y0 : list a0, ((~ (y0 = (@nil a0))) -> (@LAST a0 y0) = (@EL a0 (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0))) y0)) -> (~ ((@cons a0 x0 y0) = (@nil a0))) -> (@LAST a0 (@cons a0 x0 y0)) = (@EL a0 (Nat.sub (@List.length a0 (@cons a0 x0 y0)) (NUMERAL (BIT1 0))) (@cons a0 x0 y0)).
Definition term10 (a0 : Type') := fun y0 : list a0 => (~ (y0 = (@nil a0))) -> (@LAST a0 y0) = (@EL a0 (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0))) y0).
Definition term66 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) (x2 : a0) (x3 : a0) := x0 (@COND a0 x1 x2 x3).
Definition term5 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : list a0 => (@List.length a0 (@cons a0 x0 y0)) = (S (@List.length a0 y0))) x1.
Definition term94 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : list a0) := @COND a0 (x1 = (NUMERAL 0)) x0 (@EL a0 (Nat.sub x1 (NUMERAL (BIT1 0))) x2).
Definition term40 (a0 : Type') := imp (~ ((@nil a0) = (@nil a0))).
Definition term107 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : Prop) (x3 : a0) (x4 : a0) := (((@List.length a0 x1) = (NUMERAL 0)) = x2) -> (x2 -> x0 = x3) -> ((~ x2) -> (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1) = x4) -> (@COND a0 ((@List.length a0 x1) = (NUMERAL 0)) x0 (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1)) = (@COND a0 x2 x3 x4).
Definition term100 (a0 : Type') (x0 : a0) (x1 : list a0) := forall y0 : Prop, forall y1 : a0, forall y2 : a0, (((@List.length a0 x1) = (NUMERAL 0)) = y0) -> (y0 -> x0 = y1) -> ((~ y0) -> (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1) = y2) -> (@COND a0 ((@List.length a0 x1) = (NUMERAL 0)) x0 (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1)) = (@COND a0 y0 y1 y2).
Definition term99 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := forall y0 : Prop, forall y1 : a0, forall y2 : a0, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND a0 x0 x1 x2) = (@COND a0 y0 y1 y2).
Definition term22 (a0 : Type') (x0 : a0) (x1 : list a0) := ((~ (x1 = (@nil a0))) -> (@LAST a0 x1) = (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1)) -> (~ ((@cons a0 x0 x1) = (@nil a0))) -> (@LAST a0 (@cons a0 x0 x1)) = (@EL a0 (Nat.sub (@List.length a0 (@cons a0 x0 x1)) (NUMERAL (BIT1 0))) (@cons a0 x0 x1)).
Definition term92 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : list a0) := (fun y0 : list a0 => (@EL a0 x1 (@cons a0 x0 y0)) = (@COND a0 (x1 = (NUMERAL 0)) x0 (@EL a0 (Nat.sub x1 (NUMERAL (BIT1 0))) y0))) x2.
Definition term57 (a0 : Type') (x0 : list a0) := Nat.sub (S (@List.length a0 x0)).
Definition term83 (a0 : Type') (x0 : a0) (x1 : list a0) := ((x1 = (@nil a0)) -> x0 = (@EL a0 (@List.length a0 x1) (@cons a0 x0 x1))) /\ ((~ (x1 = (@nil a0))) -> (@LAST a0 x1) = (@EL a0 (@List.length a0 x1) (@cons a0 x0 x1))).
Definition term38 (a0 : Type') := (((~ ((@nil a0) = (@nil a0))) -> (@LAST a0 (@nil a0)) = (@EL a0 (Nat.sub (@List.length a0 (@nil a0)) (NUMERAL (BIT1 0))) (@nil a0))) /\ (forall y0 : a0, forall y1 : list a0, ((~ (y1 = (@nil a0))) -> (@LAST a0 y1) = (@EL a0 (Nat.sub (@List.length a0 y1) (NUMERAL (BIT1 0))) y1)) -> (~ ((@cons a0 y0 y1) = (@nil a0))) -> (@LAST a0 (@cons a0 y0 y1)) = (@EL a0 (Nat.sub (@List.length a0 (@cons a0 y0 y1)) (NUMERAL (BIT1 0))) (@cons a0 y0 y1)))) -> forall y0 : list a0, (~ (y0 = (@nil a0))) -> (@LAST a0 y0) = (@EL a0 (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0))) y0).
Definition term86 (a0 : Type') (x0 : list a0) := ~ (x0 = (@nil a0)).
Definition term72 (a0 : Type') (x0 : a0) (x1 : list a0) := ((x1 = (@nil a0)) -> (fun y0 : a0 => y0 = (@EL a0 (@List.length a0 x1) (@cons a0 x0 x1))) x0) /\ ((~ (x1 = (@nil a0))) -> (fun y0 : a0 => y0 = (@EL a0 (@List.length a0 x1) (@cons a0 x0 x1))) (@LAST a0 x1)).
Definition term130 (a0 : Type') (x0 : a0) (x1 : list a0) := ~ ((@cons a0 x0 x1) = (@nil a0)).
Definition term47 (a0 : Type') := @EL a0 (Nat.sub (NUMERAL 0) (NUMERAL (BIT1 0))).
Definition term42 := Nat.sub (NUMERAL 0).
Definition term82 (a0 : Type') (x0 : a0) (x1 : list a0) := and ((x1 = (@nil a0)) -> x0 = (@EL a0 (@List.length a0 x1) (@cons a0 x0 x1))).
Definition term120 (a0 : Type') (x0 : list a0) := @eq a0 (@LAST a0 x0).
Definition term14 (a0 : Type') := and ((~ ((@nil a0) = (@nil a0))) -> (@LAST a0 (@nil a0)) = (@EL a0 (Nat.sub (@List.length a0 (@nil a0)) (NUMERAL (BIT1 0))) (@nil a0))).
Definition term93 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : list a0) := @EL a0 x0 (@cons a0 x1 x2).
Definition term44 (a0 : Type') := Nat.sub (@List.length a0 (@nil a0)) (NUMERAL (BIT1 0)).
Definition term103 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : Prop) := forall y0 : a0, forall y1 : a0, (((@List.length a0 x1) = (NUMERAL 0)) = x2) -> (x2 -> x0 = y0) -> ((~ x2) -> (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1) = y1) -> (@COND a0 ((@List.length a0 x1) = (NUMERAL 0)) x0 (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1)) = (@COND a0 x2 y0 y1).
Definition term98 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) := forall y0 : a0, forall y1 : a0, (x0 = x3) -> (x3 -> x1 = y0) -> ((~ x3) -> x2 = y1) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 y0 y1).
Definition term56 (a0 : Type') (x0 : a0) (x1 : list a0) := Nat.sub (@List.length a0 (@cons a0 x0 x1)).
Definition term114 (a0 : Type') (x0 : list a0) := Nat.sub (@List.length a0 x0) (NUMERAL (BIT1 0)).
Definition term15 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => (~ (y0 = (@nil a0))) -> (@LAST a0 y0) = (@EL a0 (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0))) y0)) x0.
Definition term32 (a0 : Type') := ((~ ((@nil a0) = (@nil a0))) -> (@LAST a0 (@nil a0)) = (@EL a0 (Nat.sub (@List.length a0 (@nil a0)) (NUMERAL (BIT1 0))) (@nil a0))) /\ (forall y0 : a0, forall y1 : list a0, ((~ (y1 = (@nil a0))) -> (@LAST a0 y1) = (@EL a0 (Nat.sub (@List.length a0 y1) (NUMERAL (BIT1 0))) y1)) -> (~ ((@cons a0 y0 y1) = (@nil a0))) -> (@LAST a0 (@cons a0 y0 y1)) = (@EL a0 (Nat.sub (@List.length a0 (@cons a0 y0 y1)) (NUMERAL (BIT1 0))) (@cons a0 y0 y1))).
Definition term50 (a0 : Type') := @eq a0 (@LAST a0 (@nil a0)).
Definition term123 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : a0) := (False -> x0 = x2) -> ((~ False) -> (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1) = x3) -> (@COND a0 ((@List.length a0 x1) = (NUMERAL 0)) x0 (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1)) = (@COND a0 False x2 x3).
Definition term127 (a0 : Type') (x0 : list a0) := (~ False) -> (@EL a0 (Nat.sub (@List.length a0 x0) (NUMERAL (BIT1 0))) x0) = (@EL a0 (Nat.sub (@List.length a0 x0) (NUMERAL (BIT1 0))) x0).
Definition term122 (a0 : Type') (x0 : a0) (x1 : list a0) (x2 : a0) (x3 : a0) := (((@List.length a0 x1) = (NUMERAL 0)) = False) -> (False -> x0 = x2) -> ((~ False) -> (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1) = x3) -> (@COND a0 ((@List.length a0 x1) = (NUMERAL 0)) x0 (@EL a0 (Nat.sub (@List.length a0 x1) (NUMERAL (BIT1 0))) x1)) = (@COND a0 False x2 x3).
Definition term34 (a0 : Type') := imp (((~ ((@nil a0) = (@nil a0))) -> (@LAST a0 (@nil a0)) = (@EL a0 (Nat.sub (@List.length a0 (@nil a0)) (NUMERAL (BIT1 0))) (@nil a0))) /\ (forall y0 : a0, forall y1 : list a0, ((~ (y1 = (@nil a0))) -> (@LAST a0 y1) = (@EL a0 (Nat.sub (@List.length a0 y1) (NUMERAL (BIT1 0))) y1)) -> (~ ((@cons a0 y0 y1) = (@nil a0))) -> (@LAST a0 (@cons a0 y0 y1)) = (@EL a0 (Nat.sub (@List.length a0 (@cons a0 y0 y1)) (NUMERAL (BIT1 0))) (@cons a0 y0 y1)))).
Definition term115 (a0 : Type') (x0 : list a0) := @EL a0 (Nat.sub (@List.length a0 x0) (NUMERAL (BIT1 0))).
Definition term64 (a0 : Type') (x0 : a0) (x1 : list a0) := imp (~ ((@cons a0 x0 x1) = (@nil a0))).
Definition term17 (a0 : Type') (x0 : list a0) := imp ((fun y0 : list a0 => (~ (y0 = (@nil a0))) -> (@LAST a0 y0) = (@EL a0 (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0))) y0)) x0).
Definition term110 (a0 : Type') (x0 : a0) := True -> x0 = x0.
Definition term101 (a0 : Type') (x0 : list a0) := @EL a0 (Nat.sub (@List.length a0 x0) (NUMERAL (BIT1 0))) x0.
Definition term46 (a0 : Type') := @EL a0 (Nat.sub (@List.length a0 (@nil a0)) (NUMERAL (BIT1 0))).
Definition term61 (a0 : Type') (x0 : list a0) := @EL a0 (@List.length a0 x0).
Definition term73 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : a0 => y0 = (@EL a0 (@List.length a0 x1) (@cons a0 x0 x1))) (@LAST a0 x1).
Definition term125 (a0 : Type') (x0 : list a0) (x1 : a0) (x2 : a0) := (False -> x1 = x1) -> ((~ False) -> (@EL a0 (Nat.sub (@List.length a0 x0) (NUMERAL (BIT1 0))) x0) = x2) -> (@COND a0 ((@List.length a0 x0) = (NUMERAL 0)) x1 (@EL a0 (Nat.sub (@List.length a0 x0) (NUMERAL (BIT1 0))) x0)) = (@COND a0 False x1 x2).
Definition term69 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : a0) (x3 : list a0) (x4 : a0) := (x1 -> (fun y0 : a0 => y0 = (@EL a0 (@List.length a0 x3) (@cons a0 x2 x3))) x0) /\ ((~ x1) -> (fun y0 : a0 => y0 = (@EL a0 (@List.length a0 x3) (@cons a0 x2 x3))) x4).
Definition term36 (a0 : Type') := forall y0 : list a0, (fun y1 : list a0 => (~ (y1 = (@nil a0))) -> (@LAST a0 y1) = (@EL a0 (Nat.sub (@List.length a0 y1) (NUMERAL (BIT1 0))) y1)) y0.
Definition term20 (a0 : Type') (x0 : a0) (x1 : list a0) := (~ ((@cons a0 x0 x1) = (@nil a0))) -> (@LAST a0 (@cons a0 x0 x1)) = (@EL a0 (Nat.sub (@List.length a0 (@cons a0 x0 x1)) (NUMERAL (BIT1 0))) (@cons a0 x0 x1)).
Definition term89 (a0 : Type') (x0 : nat) := forall y0 : a0, forall y1 : list a0, (@EL a0 x0 (@cons a0 y0 y1)) = (@COND a0 (x0 = (NUMERAL 0)) y0 (@EL a0 (Nat.sub x0 (NUMERAL (BIT1 0))) y1)).
Definition term30 (a0 : Type') := forall y0 : a0, forall y1 : list a0, ((~ (y1 = (@nil a0))) -> (@LAST a0 y1) = (@EL a0 (Nat.sub (@List.length a0 y1) (NUMERAL (BIT1 0))) y1)) -> (~ ((@cons a0 y0 y1) = (@nil a0))) -> (@LAST a0 (@cons a0 y0 y1)) = (@EL a0 (Nat.sub (@List.length a0 (@cons a0 y0 y1)) (NUMERAL (BIT1 0))) (@cons a0 y0 y1)).
Definition term29 (a0 : Type') := forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => (~ (y2 = (@nil a0))) -> (@LAST a0 y2) = (@EL a0 (Nat.sub (@List.length a0 y2) (NUMERAL (BIT1 0))) y2)) y1) -> (fun y2 : list a0 => (~ (y2 = (@nil a0))) -> (@LAST a0 y2) = (@EL a0 (Nat.sub (@List.length a0 y2) (NUMERAL (BIT1 0))) y2)) (@cons a0 y0 y1).
Definition term2 (a0 : Type') := forall y0 : a0, forall y1 : list a0, (@List.length a0 (@cons a0 y0 y1)) = (S (@List.length a0 y1)).
Definition term74 (a0 : Type') (x0 : list a0) := imp (~ (x0 = (@nil a0))).
Definition term96 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) (x5 : a0) := (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = x5) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 x5).
Definition term43 := NUMERAL (BIT1 0).
Definition term54 (a0 : Type') (x0 : a0) (x1 : list a0) := @eq a0 (@LAST a0 (@cons a0 x0 x1)).
Definition term31 (a0 : Type') := ((fun y0 : list a0 => (~ (y0 = (@nil a0))) -> (@LAST a0 y0) = (@EL a0 (Nat.sub (@List.length a0 y0) (NUMERAL (BIT1 0))) y0)) (@nil a0)) /\ (forall y0 : a0, forall y1 : list a0, ((fun y2 : list a0 => (~ (y2 = (@nil a0))) -> (@LAST a0 y2) = (@EL a0 (Nat.sub (@List.length a0 y2) (NUMERAL (BIT1 0))) y2)) y1) -> (fun y2 : list a0 => (~ (y2 = (@nil a0))) -> (@LAST a0 y2) = (@EL a0 (Nat.sub (@List.length a0 y2) (NUMERAL (BIT1 0))) y2)) (@cons a0 y0 y1)).
