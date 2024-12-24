Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term159 (x0 : nat) := False \/ (~ (x0 = (NUMERAL 0))).
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) := @COND Prop (x0 = (NUMERAL 0)) ((x2 = (NUMERAL 0)) -> x1 = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (~ (Peano.lt x1 x2))).
Definition term75 (x0 : Prop) (x1 : Prop) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : Prop) := (x1 -> (fun y0 : Prop => (((Peano.lt x2 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x3 x4))) /\ ((~ (x2 = (NUMERAL 0))) \/ ((x3 = (NUMERAL 0)) \/ (~ (x4 = (NUMERAL 0)))))) = y0) x0) /\ ((~ x1) -> (fun y0 : Prop => (((Peano.lt x2 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x3 x4))) /\ ((~ (x2 = (NUMERAL 0))) \/ ((x3 = (NUMERAL 0)) \/ (~ (x4 = (NUMERAL 0)))))) = y0) x5).
Definition term41 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (Peano.lt x0 (NUMERAL (BIT0 (BIT1 0))))) /\ (Peano.lt x1 x2)).
Definition term140 (x0 : nat) := (x0 = (S (NUMERAL 0))) \/ False.
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x1 x2)).
Definition term129 := or (~ True).
Definition term4 (x0 : nat) := forall y0 : nat, (Peano.le y0 x0) = (~ (Peano.lt x0 y0)).
Definition term163 (x0 : nat) := @eq Prop (~ (x0 = (NUMERAL 0))).
Definition term82 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) -> (fun y0 : Prop => (((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x1 x2))) /\ ((~ (x0 = (NUMERAL 0))) \/ ((x1 = (NUMERAL 0)) \/ (~ (x2 = (NUMERAL 0)))))) = y0) ((x0 = (NUMERAL (BIT1 0))) \/ (~ (Peano.lt x1 x2))).
Definition term43 (x0 : Prop) := ~ (~ x0).
Definition term13 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.pow y0 y1) (Nat.pow y0 y2)) = (((Peano.le (NUMERAL (BIT0 (BIT1 0))) y0) /\ (Peano.lt y1 y2)) \/ ((y0 = (NUMERAL 0)) /\ ((~ (y1 = (NUMERAL 0))) /\ (y2 = (NUMERAL 0)))))) x0.
Definition term131 (x0 : nat) (x1 : nat) := False \/ ((x0 = (NUMERAL 0)) \/ (~ (x1 = (NUMERAL 0)))).
Definition term54 (x0 : nat) (x1 : nat) := ~ ((~ (x0 = (NUMERAL 0))) /\ (x1 = (NUMERAL 0))).
Definition term88 (x0 : nat) (x1 : nat) (x2 : nat) := and ((x0 = (NUMERAL 0)) -> (fun y0 : Prop => (((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x2 x1))) /\ ((~ (x0 = (NUMERAL 0))) \/ ((x2 = (NUMERAL 0)) \/ (~ (x1 = (NUMERAL 0)))))) = y0) ((x1 = (NUMERAL 0)) -> x2 = (NUMERAL 0))).
Definition term93 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : Prop => (((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x2 x1))) /\ ((~ y0) \/ ((x2 = (NUMERAL 0)) \/ (~ (x1 = (NUMERAL 0)))))) = ((x1 = (NUMERAL 0)) -> x2 = (NUMERAL 0)).
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) := @COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) -> x2 = (NUMERAL 0)).
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL (BIT1 0))) \/ (~ (Peano.lt x1 x2)).
Definition term152 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (y0 \/ (~ (x0 = (NUMERAL 0)))) = ((x0 = (NUMERAL 0)) -> y0)) (x1 = (NUMERAL 0)).
Definition term118 := S (NUMERAL 0).
Definition term55 (x0 : nat) (x1 : nat) := (~ (~ (x0 = (NUMERAL 0)))) \/ (~ (x1 = (NUMERAL 0))).
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (Peano.lt x0 (NUMERAL (BIT0 (BIT1 0))))) /\ (Peano.lt x1 x2)) \/ ((x0 = (NUMERAL 0)) /\ ((~ (x1 = (NUMERAL 0))) /\ (x2 = (NUMERAL 0)))).
Definition term154 (x0 : nat) := True \/ (~ (x0 = (NUMERAL 0))).
Definition term60 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x1 = (NUMERAL 0))).
Definition term158 (x0 : nat) := (fun y0 : Prop => (y0 \/ (~ (x0 = (NUMERAL 0)))) = ((x0 = (NUMERAL 0)) -> y0)) False.
Definition term32 (x0 : nat) (x1 : nat) (x2 : nat) := or ((~ (Peano.lt x0 (NUMERAL (BIT0 (BIT1 0))))) /\ (Peano.lt x1 x2)).
Definition term148 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = (S (NUMERAL 0))) \/ (~ (Peano.lt x1 x2))).
Definition term134 (x0 : nat) (x1 : nat) := @eq Prop ((x0 = (NUMERAL 0)) \/ (~ (x1 = (NUMERAL 0)))).
Definition term119 := S (S (NUMERAL 0)).
Definition term138 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (Peano.lt x0 (NUMERAL 0)).
Definition term47 (x0 : nat) := or (Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term96 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x1 x2))) /\ ((~ True) \/ ((x1 = (NUMERAL 0)) \/ (~ (x2 = (NUMERAL 0))))).
Definition term87 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) -> (((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x2 x1))) /\ ((~ (x0 = (NUMERAL 0))) \/ ((x2 = (NUMERAL 0)) \/ (~ (x1 = (NUMERAL 0)))))) = ((x1 = (NUMERAL 0)) -> x2 = (NUMERAL 0)).
Definition term128 (x0 : nat) (x1 : nat) := True \/ (~ (Peano.lt x0 x1)).
Definition term11 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((~ (x0 /\ y0)) = ((~ x0) \/ (~ y0))) /\ ((~ (x0 \/ y0)) = ((~ x0) /\ (~ y0)))) x1.
Definition term80 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => (((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x1 x2))) /\ ((~ (x0 = (NUMERAL 0))) \/ ((x1 = (NUMERAL 0)) \/ (~ (x2 = (NUMERAL 0)))))) = y0) ((x0 = (NUMERAL (BIT1 0))) \/ (~ (Peano.lt x1 x2))).
Definition term40 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term12 (x0 : Prop) (x1 : Prop) := ((~ (x0 /\ x1)) = ((~ x0) \/ (~ x1))) /\ ((~ (x0 \/ x1)) = ((~ x0) /\ (~ x1))).
Definition term28 (x0 : nat) := and (~ (Peano.lt x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term103 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x1 x2))) /\ ((~ False) \/ ((x1 = (NUMERAL 0)) \/ (~ (x2 = (NUMERAL 0))))).
Definition term81 (x0 : nat) := imp (~ (x0 = (NUMERAL 0))).
Definition term112 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term77 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => (((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x1 x2))) /\ ((~ (x0 = (NUMERAL 0))) \/ ((x1 = (NUMERAL 0)) \/ (~ (x2 = (NUMERAL 0)))))) = y0) (@COND Prop (x0 = (NUMERAL 0)) ((x2 = (NUMERAL 0)) -> x1 = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (~ (Peano.lt x1 x2)))).
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))))) \/ (~ (Peano.lt x1 x2)).
Definition term160 (x0 : nat) := (x0 = (NUMERAL 0)) -> False.
Definition term146 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = (S (NUMERAL 0))) \/ (~ (Peano.lt x1 x2))) /\ True.
Definition term37 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.pow x1 x0) (Nat.pow x1 x2).
Definition term9 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((~ (y0 /\ y1)) = ((~ y0) \/ (~ y1))) /\ ((~ (y0 \/ y1)) = ((~ y0) /\ (~ y1)))) x0.
Definition term39 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term147 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x1 x2))) /\ ((~ False) \/ ((x1 = (NUMERAL 0)) \/ (~ (x2 = (NUMERAL 0)))))).
Definition term133 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x1 x2))) /\ ((~ True) \/ ((x1 = (NUMERAL 0)) \/ (~ (x2 = (NUMERAL 0)))))).
Definition term10 (x0 : Prop) := forall y0 : Prop, ((~ (x0 /\ y0)) = ((~ x0) \/ (~ y0))) /\ ((~ (x0 \/ y0)) = ((~ x0) /\ (~ y0))).
Definition term143 := or (~ False).
Definition term78 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = (NUMERAL 0)) -> (fun y0 : Prop => (((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x1 x2))) /\ ((~ (x0 = (NUMERAL 0))) \/ ((x1 = (NUMERAL 0)) \/ (~ (x2 = (NUMERAL 0)))))) = y0) ((x2 = (NUMERAL 0)) -> x1 = (NUMERAL 0))) /\ ((~ (x0 = (NUMERAL 0))) -> (fun y0 : Prop => (((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x1 x2))) /\ ((~ (x0 = (NUMERAL 0))) \/ ((x1 = (NUMERAL 0)) \/ (~ (x2 = (NUMERAL 0)))))) = y0) ((x0 = (NUMERAL (BIT1 0))) \/ (~ (Peano.lt x1 x2)))).
Definition term104 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : Prop => (((Peano.lt x2 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x0 x1))) /\ ((~ y0) \/ ((x0 = (NUMERAL 0)) \/ (~ (x1 = (NUMERAL 0)))))) = ((x2 = (NUMERAL (BIT1 0))) \/ (~ (Peano.lt x0 x1)))) (x2 = (NUMERAL 0))).
Definition term97 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : Prop => (((Peano.lt x2 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x1 x0))) /\ ((~ y0) \/ ((x1 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0)))))) = ((x0 = (NUMERAL 0)) -> x1 = (NUMERAL 0))) (x2 = (NUMERAL 0))).
Definition term16 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.lt (Nat.pow x0 x1) (Nat.pow x0 y0)) = (((Peano.le (NUMERAL (BIT0 (BIT1 0))) x0) /\ (Peano.lt x1 y0)) \/ ((x0 = (NUMERAL 0)) /\ ((~ (x1 = (NUMERAL 0))) /\ (y0 = (NUMERAL 0))))).
Definition term15 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (Nat.pow x0 y0) (Nat.pow x0 y1)) = (((Peano.le (NUMERAL (BIT0 (BIT1 0))) x0) /\ (Peano.lt y0 y1)) \/ ((x0 = (NUMERAL 0)) /\ ((~ (y0 = (NUMERAL 0))) /\ (y1 = (NUMERAL 0)))))) x1.
Definition term65 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x1 x2))) /\ ((~ (x0 = (NUMERAL 0))) \/ ((x1 = (NUMERAL 0)) \/ (~ (x2 = (NUMERAL 0)))))).
Definition term56 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term5 := fun y0 : nat => forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0).
Definition term111 (x0 : nat) (x1 : nat) := (x0 = x1) \/ (Peano.lt x0 x1).
Definition term73 (x0 : Prop) (x1 : Prop) (x2 : Prop -> Prop) (x3 : Prop) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (NUMERAL (BIT0 (BIT1 0))) x0) /\ (Peano.lt x1 x2).
Definition term85 (x0 : nat) := imp (x0 = (NUMERAL 0)).
Definition term161 (x0 : nat) := @eq Prop (True \/ (~ (x0 = (NUMERAL 0)))).
Definition term156 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : Prop => (y0 \/ (~ (x0 = (NUMERAL 0)))) = ((x0 = (NUMERAL 0)) -> y0)) (x1 = (NUMERAL 0))).
Definition term94 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => (((Peano.lt x2 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x1 x0))) /\ ((~ y0) \/ ((x1 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0)))))) = ((x0 = (NUMERAL 0)) -> x1 = (NUMERAL 0))) (x2 = (NUMERAL 0)).
Definition term142 (x0 : nat) (x1 : nat) (x2 : nat) := and ((x0 = (S (NUMERAL 0))) \/ (~ (Peano.lt x1 x2))).
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) := and ((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x1 x2))).
Definition term66 (x0 : nat) := or (x0 = (NUMERAL (BIT1 0))).
Definition term153 (x0 : nat) := (fun y0 : Prop => (y0 \/ (~ (x0 = (NUMERAL 0)))) = ((x0 = (NUMERAL 0)) -> y0)) True.
Definition term145 (x0 : nat) (x1 : nat) := True \/ ((x0 = (NUMERAL 0)) \/ (~ (x1 = (NUMERAL 0)))).
Definition term92 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x1 x2))) /\ ((~ (x0 = (NUMERAL 0))) \/ ((x1 = (NUMERAL 0)) \/ (~ (x2 = (NUMERAL 0)))))) = (@COND Prop (x0 = (NUMERAL 0)) ((x2 = (NUMERAL 0)) -> x1 = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (~ (Peano.lt x1 x2))))).
Definition term113 (x0 : nat) := (fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) = False) x0.
Definition term1 (x0 : nat) := fun y0 : nat => (~ (Peano.lt x0 y0)) = (Peano.le y0 x0).
Definition term125 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term122 := Peano.lt (NUMERAL 0) (S (NUMERAL 0)).
Definition term58 (x0 : nat) := or (~ (~ (x0 = (NUMERAL 0)))).
Definition term102 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => (((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x1 x2))) /\ ((~ y0) \/ ((x1 = (NUMERAL 0)) \/ (~ (x2 = (NUMERAL 0)))))) = ((x0 = (NUMERAL (BIT1 0))) \/ (~ (Peano.lt x1 x2)))) False.
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => (((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x1 x2))) /\ ((~ (x0 = (NUMERAL 0))) \/ ((x1 = (NUMERAL 0)) \/ (~ (x2 = (NUMERAL 0)))))) = y0) (@COND Prop x3 x4 x5).
Definition term141 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (S (NUMERAL 0))) \/ (~ (Peano.lt x1 x2)).
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 x2).
Definition term59 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) /\ ((~ (x1 = (NUMERAL 0))) /\ (x2 = (NUMERAL 0))).
Definition term36 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term166 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le (Nat.pow y0 y1) (Nat.pow y0 y2)) = (@COND Prop (y0 = (NUMERAL 0)) ((y1 = (NUMERAL 0)) -> y2 = (NUMERAL 0)) ((y0 = (NUMERAL (BIT1 0))) \/ (Peano.le y1 y2))).
Definition term165 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.pow x0 y0) (Nat.pow x0 y1)) = (@COND Prop (x0 = (NUMERAL 0)) ((y0 = (NUMERAL 0)) -> y1 = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le y0 y1))).
Definition term106 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term14 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.pow x0 y0) (Nat.pow x0 y1)) = (((Peano.le (NUMERAL (BIT0 (BIT1 0))) x0) /\ (Peano.lt y0 y1)) \/ ((x0 = (NUMERAL 0)) /\ ((~ (y0 = (NUMERAL 0))) /\ (y1 = (NUMERAL 0))))).
Definition term8 := forall y0 : nat, forall y1 : nat, (Peano.le y1 y0) = (~ (Peano.lt y0 y1)).
Definition term7 := forall y0 : nat, forall y1 : nat, (~ (Peano.lt y0 y1)) = (Peano.le y1 y0).
Definition term90 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = (NUMERAL 0)) -> (((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x1 x2))) /\ ((~ (x0 = (NUMERAL 0))) \/ ((x1 = (NUMERAL 0)) \/ (~ (x2 = (NUMERAL 0)))))) = ((x2 = (NUMERAL 0)) -> x1 = (NUMERAL 0))) /\ ((~ (x0 = (NUMERAL 0))) -> (((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x1 x2))) /\ ((~ (x0 = (NUMERAL 0))) \/ ((x1 = (NUMERAL 0)) \/ (~ (x2 = (NUMERAL 0)))))) = ((x0 = (NUMERAL (BIT1 0))) \/ (~ (Peano.lt x1 x2)))).
Definition term126 := or ((NUMERAL 0) = (S (NUMERAL 0))).
Definition term135 (x0 : nat) := Peano.lt x0 (S (S (NUMERAL 0))).
Definition term3 (x0 : nat) := forall y0 : nat, (~ (Peano.lt x0 y0)) = (Peano.le y0 x0).
Definition term162 (x0 : nat) := @eq Prop (False \/ (~ (x0 = (NUMERAL 0)))).
Definition term115 := Peano.lt (NUMERAL 0).
Definition term136 (x0 : nat) := (x0 = (S (NUMERAL 0))) \/ (Peano.lt x0 (S (NUMERAL 0))).
Definition term127 := ((NUMERAL 0) = (S (NUMERAL 0))) \/ True.
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (Peano.lt x0 (NUMERAL (BIT0 (BIT1 0))))) /\ (Peano.lt x1 x2))) /\ (~ ((x0 = (NUMERAL 0)) /\ ((~ (x1 = (NUMERAL 0))) /\ (x2 = (NUMERAL 0))))).
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt x0 (NUMERAL (BIT0 (BIT1 0))))) /\ (Peano.lt x1 x2).
Definition term110 (x0 : nat) (x1 : nat) := Peano.lt x0 (S x1).
Definition term116 := S (NUMERAL (BIT1 0)).
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) := @COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) -> x2 = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 x2)).
Definition term95 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => (((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x2 x1))) /\ ((~ y0) \/ ((x2 = (NUMERAL 0)) \/ (~ (x1 = (NUMERAL 0)))))) = ((x1 = (NUMERAL 0)) -> x2 = (NUMERAL 0))) True.
Definition term2 (x0 : nat) := fun y0 : nat => (Peano.le y0 x0) = (~ (Peano.lt x0 y0)).
Definition term49 (x0 : nat) (x1 : nat) (x2 : nat) := and (~ ((~ (Peano.lt x0 (NUMERAL (BIT0 (BIT1 0))))) /\ (Peano.lt x1 x2))).
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((x0 = (NUMERAL 0)) /\ ((~ (x1 = (NUMERAL 0))) /\ (x2 = (NUMERAL 0)))).
Definition term157 (x0 : nat) (x1 : nat) := @eq Prop (((x1 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0)))) = ((x0 = (NUMERAL 0)) -> x1 = (NUMERAL 0))).
Definition term86 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) -> (fun y0 : Prop => (((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x2 x1))) /\ ((~ (x0 = (NUMERAL 0))) \/ ((x2 = (NUMERAL 0)) \/ (~ (x1 = (NUMERAL 0)))))) = y0) ((x1 = (NUMERAL 0)) -> x2 = (NUMERAL 0)).
Definition term108 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term89 (x0 : nat) (x1 : nat) (x2 : nat) := and ((x0 = (NUMERAL 0)) -> (((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x2 x1))) /\ ((~ (x0 = (NUMERAL 0))) \/ ((x2 = (NUMERAL 0)) \/ (~ (x1 = (NUMERAL 0)))))) = ((x1 = (NUMERAL 0)) -> x2 = (NUMERAL 0))).
Definition term61 (x0 : nat) := or (~ (x0 = (NUMERAL 0))).
Definition term83 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) -> (((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x1 x2))) /\ ((~ (x0 = (NUMERAL 0))) \/ ((x1 = (NUMERAL 0)) \/ (~ (x2 = (NUMERAL 0)))))) = ((x0 = (NUMERAL (BIT1 0))) \/ (~ (Peano.lt x1 x2))).
Definition term27 (x0 : nat) := and (Peano.le (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term79 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) -> x1 = (NUMERAL 0).
Definition term155 (x0 : nat) := (x0 = (NUMERAL 0)) -> True.
Definition term139 (x0 : nat) := or (x0 = (S (NUMERAL 0))).
Definition term26 := NUMERAL (BIT0 (BIT1 0)).
Definition term137 (x0 : nat) := Peano.lt x0 (S (NUMERAL 0)).
Definition term109 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0))) x1.
Definition term62 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) \/ ((x1 = (NUMERAL 0)) \/ (~ (x2 = (NUMERAL 0)))).
Definition term101 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => (((Peano.lt x2 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x0 x1))) /\ ((~ y0) \/ ((x0 = (NUMERAL 0)) \/ (~ (x1 = (NUMERAL 0)))))) = ((x2 = (NUMERAL (BIT1 0))) \/ (~ (Peano.lt x0 x1)))) (x2 = (NUMERAL 0)).
Definition term123 := ((NUMERAL 0) = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term114 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term0 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term120 := Peano.lt (NUMERAL 0) (S (S (NUMERAL 0))).
Definition term100 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : Prop => (((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x1 x2))) /\ ((~ y0) \/ ((x1 = (NUMERAL 0)) \/ (~ (x2 = (NUMERAL 0)))))) = ((x0 = (NUMERAL (BIT1 0))) \/ (~ (Peano.lt x1 x2))).
Definition term107 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1))) x0.
Definition term20 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y1 y0) = (~ (Peano.lt y0 y1))) x0.
Definition term53 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) /\ (x1 = (NUMERAL 0)).
Definition term25 (x0 : nat) := ~ (Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term91 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : Prop => (((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x1 x2))) /\ ((~ (x0 = (NUMERAL 0))) \/ ((x1 = (NUMERAL 0)) \/ (~ (x2 = (NUMERAL 0)))))) = y0) (@COND Prop (x0 = (NUMERAL 0)) ((x2 = (NUMERAL 0)) -> x1 = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (~ (Peano.lt x1 x2))))).
Definition term24 (x0 : nat) := Peano.le (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (((~ (Peano.lt x0 (NUMERAL (BIT0 (BIT1 0))))) /\ (Peano.lt x1 x2)) \/ ((x0 = (NUMERAL 0)) /\ ((~ (x1 = (NUMERAL 0))) /\ (x2 = (NUMERAL 0))))).
Definition term44 (x0 : nat) := ~ (~ (Peano.lt x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term21 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le y0 x0) = (~ (Peano.lt x0 y0))) x1.
Definition term31 (x0 : nat) (x1 : nat) (x2 : nat) := or ((Peano.le (NUMERAL (BIT0 (BIT1 0))) x0) /\ (Peano.lt x1 x2)).
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.lt (Nat.pow x0 x1) (Nat.pow x0 y0)) = (((Peano.le (NUMERAL (BIT0 (BIT1 0))) x0) /\ (Peano.lt x1 y0)) \/ ((x0 = (NUMERAL 0)) /\ ((~ (x1 = (NUMERAL 0))) /\ (y0 = (NUMERAL 0)))))) x2.
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : Prop => (((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x1 x2))) /\ ((~ (x0 = (NUMERAL 0))) \/ ((x1 = (NUMERAL 0)) \/ (~ (x2 = (NUMERAL 0)))))) = y0.
Definition term99 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term132 (x0 : nat) (x1 : nat) := True /\ ((x0 = (NUMERAL 0)) \/ (~ (x1 = (NUMERAL 0)))).
Definition term64 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (Peano.le (Nat.pow x1 x0) (Nat.pow x1 x2)).
Definition term105 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x1 x2))) /\ ((~ (x0 = (NUMERAL 0))) \/ ((x1 = (NUMERAL 0)) \/ (~ (x2 = (NUMERAL 0)))))) = ((x0 = (NUMERAL (BIT1 0))) \/ (~ (Peano.lt x1 x2)))).
Definition term149 (x0 : nat) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) (x0 = (NUMERAL 0)).
Definition term144 (x0 : nat) (x1 : nat) := (~ False) \/ ((x0 = (NUMERAL 0)) \/ (~ (x1 = (NUMERAL 0)))).
Definition term121 := ((NUMERAL 0) = (S (NUMERAL 0))) \/ (Peano.lt (NUMERAL 0) (S (NUMERAL 0))).
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (Peano.lt (Nat.pow x1 x0) (Nat.pow x1 x2)).
Definition term6 := fun y0 : nat => forall y1 : nat, (Peano.le y1 y0) = (~ (Peano.lt y0 y1)).
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.pow x1 x0) (Nat.pow x1 x2).
Definition term72 (x0 : Prop -> Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := x0 (@COND Prop x1 x2 x3).
Definition term45 (x0 : nat) := Peano.lt x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term57 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term124 := or ((NUMERAL 0) = (NUMERAL 0)).
Definition term98 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x2 x1))) /\ ((~ (x0 = (NUMERAL 0))) \/ ((x2 = (NUMERAL 0)) \/ (~ (x1 = (NUMERAL 0)))))) = ((x1 = (NUMERAL 0)) -> x2 = (NUMERAL 0))).
Definition term46 (x0 : nat) := or (~ (~ (Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term164 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.pow x0 x1) (Nat.pow x0 y0)) = (@COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) -> y0 = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 y0))).
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) \/ (~ ((~ (x1 = (NUMERAL 0))) /\ (x2 = (NUMERAL 0)))).
Definition term130 (x0 : nat) (x1 : nat) := (~ True) \/ ((x0 = (NUMERAL 0)) \/ (~ (x1 = (NUMERAL 0)))).
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le (NUMERAL (BIT0 (BIT1 0))) x0) /\ (Peano.lt x1 x2)) \/ ((x0 = (NUMERAL 0)) /\ ((~ (x1 = (NUMERAL 0))) /\ (x2 = (NUMERAL 0)))).
Definition term63 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x1 x2))) /\ ((~ (x0 = (NUMERAL 0))) \/ ((x1 = (NUMERAL 0)) \/ (~ (x2 = (NUMERAL 0))))).
Definition term150 (x0 : nat) := ((x0 = (NUMERAL 0)) = True) \/ ((x0 = (NUMERAL 0)) = False).
Definition term117 := NUMERAL (BIT1 0).
Definition term84 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => (((Peano.lt x0 (NUMERAL (BIT0 (BIT1 0)))) \/ (~ (Peano.lt x2 x1))) /\ ((~ (x0 = (NUMERAL 0))) \/ ((x2 = (NUMERAL 0)) \/ (~ (x1 = (NUMERAL 0)))))) = y0) ((x1 = (NUMERAL 0)) -> x2 = (NUMERAL 0)).
Definition term151 (x0 : nat) := fun y0 : Prop => (y0 \/ (~ (x0 = (NUMERAL 0)))) = ((x0 = (NUMERAL 0)) -> y0).
