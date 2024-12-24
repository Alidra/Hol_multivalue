Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term179 (x0 : nat) (x1 : nat) := @eq Prop ((False \/ (Peano.le x1 x0)) /\ (False \/ (Peano.le x0 x1))).
Definition term69 (x0 : nat) (x1 : nat) := (((Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)) -> (Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> (Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)).
Definition term160 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (NUMERAL (BIT1 0)) x0) \/ ((Peano.le x2 x1) /\ (Peano.le x1 x2)).
Definition term150 (x0 : nat) := Peano.le (NUMERAL (BIT1 0)) x0.
Definition term18 (x0 : Prop) (x1 : Prop) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : Prop) := (x1 -> (fun y0 : Prop => ((Peano.le (Nat.pow x3 x4) (Nat.pow x3 x2)) /\ (Peano.le (Nat.pow x3 x2) (Nat.pow x3 x4))) = y0) x0) /\ ((~ x1) -> (fun y0 : Prop => ((Peano.le (Nat.pow x3 x4) (Nat.pow x3 x2)) /\ (Peano.le (Nat.pow x3 x2) (Nat.pow x3 x4))) = y0) x5).
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : Prop => ((Peano.le (Nat.pow x0 x1) (Nat.pow x0 x2)) /\ (Peano.le (Nat.pow x0 x2) (Nat.pow x0 x1))) = y0) (@COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) = (x2 = (NUMERAL 0))) ((x0 = (NUMERAL (BIT1 0))) \/ (x1 = x2)))).
Definition term79 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x0 (NUMERAL (BIT1 0))) /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ ((Peano.le x2 x1) /\ (Peano.le x1 x2)).
Definition term130 (x0 : nat) := imp (False /\ (Peano.le (NUMERAL 0) x0)).
Definition term119 (x0 : nat) := and ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)).
Definition term104 (x0 : nat) (x1 : nat) := @eq Prop (((Peano.le (NUMERAL 0) x1) -> (Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> Peano.le (NUMERAL 0) x1)).
Definition term44 := @eq nat (NUMERAL 0).
Definition term57 (x0 : nat) (x1 : nat) := ((x1 = (NUMERAL 0)) -> x0 = (NUMERAL 0)) /\ ((x0 = (NUMERAL 0)) -> x1 = (NUMERAL 0)).
Definition term151 (x0 : nat) := or (True /\ (Peano.le (NUMERAL (BIT1 0)) x0)).
Definition term37 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.pow y0 y1) (Nat.pow y0 y2)) = (@COND Prop (y0 = (NUMERAL 0)) ((y1 = (NUMERAL 0)) -> y2 = (NUMERAL 0)) ((y0 = (NUMERAL (BIT1 0))) \/ (Peano.le y1 y2)))) x0.
Definition term131 (x0 : nat) (x1 : nat) := (False /\ (Peano.le (NUMERAL 0) x0)) -> (Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1).
Definition term0 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) /\ (Peano.le x0 x1).
Definition term101 (x0 : nat) (x1 : nat) := ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> Peano.le (NUMERAL 0) x1.
Definition term31 (x0 : nat) (x1 : nat) (x2 : nat) := and ((x0 = (NUMERAL 0)) -> (fun y0 : Prop => ((Peano.le (Nat.pow x0 x1) (Nat.pow x0 x2)) /\ (Peano.le (Nat.pow x0 x2) (Nat.pow x0 x1))) = y0) ((x1 = (NUMERAL 0)) = (x2 = (NUMERAL 0)))).
Definition term182 (x0 : nat) := or (False /\ (Peano.le (NUMERAL (BIT1 0)) x0)).
Definition term47 (x0 : nat) (x1 : nat) (x2 : nat) := @COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) -> x2 = (NUMERAL 0)).
Definition term135 (x0 : nat) := @eq Prop (False /\ (Peano.le (NUMERAL 0) x0)).
Definition term51 := or ((NUMERAL 0) = (NUMERAL (BIT1 0))).
Definition term94 (x0 : nat) := imp (True /\ (Peano.le (NUMERAL 0) x0)).
Definition term127 (x0 : nat) := True /\ (~ ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0))).
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) -> ((Peano.le (Nat.pow x0 x1) (Nat.pow x0 x2)) /\ (Peano.le (Nat.pow x0 x2) (Nat.pow x0 x1))) = ((x1 = (NUMERAL 0)) = (x2 = (NUMERAL 0))).
Definition term122 (x0 : nat) := @eq Prop ((True -> (Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> True)).
Definition term102 (x0 : nat) (x1 : nat) := ((Peano.le (NUMERAL 0) x1) -> (Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> Peano.le (NUMERAL 0) x1).
Definition term1 (x0 : nat) := fun y0 : nat => ((Peano.le x0 y0) /\ (Peano.le y0 x0)) = (x0 = y0).
Definition term3 (x0 : nat) := forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x0)) = (x0 = y0).
Definition term115 (x0 : nat) := (fun y0 : Prop => ((y0 -> (Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> y0)) = (y0 = ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)))) False.
Definition term77 (x0 : nat) (x1 : nat) (x2 : nat) := (((Peano.le x0 (NUMERAL (BIT1 0))) /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.le x2 x1)) /\ (((Peano.le x0 (NUMERAL (BIT1 0))) /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.le x1 x2)).
Definition term153 (x0 : nat) (x1 : nat) (x2 : nat) := (True /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.le x1 x2).
Definition term65 (x0 : nat) := (Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0).
Definition term149 (x0 : nat) := True /\ (Peano.le (NUMERAL (BIT1 0)) x0).
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = (NUMERAL 0)) -> ((Peano.le (Nat.pow x0 x1) (Nat.pow x0 x2)) /\ (Peano.le (Nat.pow x0 x2) (Nat.pow x0 x1))) = ((x1 = (NUMERAL 0)) = (x2 = (NUMERAL 0)))) /\ ((~ (x0 = (NUMERAL 0))) -> ((Peano.le (Nat.pow x0 x1) (Nat.pow x0 x2)) /\ (Peano.le (Nat.pow x0 x2) (Nat.pow x0 x1))) = ((x0 = (NUMERAL (BIT1 0))) \/ (x1 = x2))).
Definition term171 (x0 : nat) (x1 : nat) := (False \/ (Peano.le x1 x0)) /\ (False \/ (Peano.le x0 x1)).
Definition term92 (x0 : nat) := False /\ (Peano.le (NUMERAL 0) x0).
Definition term85 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (((y0 /\ (Peano.le (NUMERAL 0) x0)) -> (Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)) /\ (((Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)) -> y0 /\ (Peano.le (NUMERAL 0) x0))) = ((y0 /\ (Peano.le (NUMERAL 0) x0)) = ((Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)))) True.
Definition term125 (x0 : nat) := ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> False.
Definition term121 (x0 : nat) := ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ True.
Definition term133 (x0 : nat) (x1 : nat) := ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> False /\ (Peano.le (NUMERAL 0) x1).
Definition term154 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (NUMERAL (BIT1 0)) x0) \/ (Peano.le x1 x2).
Definition term53 (x0 : nat) (x1 : nat) := ((NUMERAL 0) = (NUMERAL (BIT1 0))) \/ (Peano.le x0 x1).
Definition term24 (x0 : nat) := imp (~ (x0 = (NUMERAL 0))).
Definition term2 (x0 : nat) := fun y0 : nat => (x0 = y0) = ((Peano.le x0 y0) /\ (Peano.le y0 x0)).
Definition term105 (x0 : nat) := @eq Prop (True /\ (Peano.le (NUMERAL 0) x0)).
Definition term58 (x0 : nat) (x1 : nat) := @eq Prop (((x1 = (NUMERAL 0)) -> x0 = (NUMERAL 0)) /\ ((x0 = (NUMERAL 0)) -> x1 = (NUMERAL 0))).
Definition term132 (x0 : nat) (x1 : nat) := and ((False /\ (Peano.le (NUMERAL 0) x0)) -> (Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)).
Definition term98 (x0 : nat) (x1 : nat) := and ((True /\ (Peano.le (NUMERAL 0) x0)) -> (Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)).
Definition term72 (x0 : nat) := @eq Prop ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)).
Definition term146 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => (((y0 /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.le x2 x1)) /\ ((y0 /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.le x1 x2))) = ((y0 /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ ((Peano.le x2 x1) /\ (Peano.le x1 x2)))) False.
Definition term174 (x0 : nat) (x1 : nat) := and (True \/ (Peano.le x0 x1)).
Definition term107 (x0 : nat) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) (Peano.le (NUMERAL 0) x0).
Definition term45 (x0 : nat) := @COND Prop (x0 = (NUMERAL 0)).
Definition term39 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.pow x0 y0) (Nat.pow x0 y1)) = (@COND Prop (x0 = (NUMERAL 0)) ((y0 = (NUMERAL 0)) -> y1 = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le y0 y1)))) x1.
Definition term126 (x0 : nat) := ~ ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)).
Definition term118 (x0 : nat) := and (True -> (Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)).
Definition term134 (x0 : nat) (x1 : nat) := @eq Prop (((False /\ (Peano.le (NUMERAL 0) x1)) -> (Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> False /\ (Peano.le (NUMERAL 0) x1))).
Definition term103 (x0 : nat) (x1 : nat) := @eq Prop (((True /\ (Peano.le (NUMERAL 0) x1)) -> (Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> True /\ (Peano.le (NUMERAL 0) x1))).
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat) := and (((Peano.le x0 (NUMERAL (BIT1 0))) /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.le x1 x2)).
Definition term36 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term5 := fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1).
Definition term74 (x0 : nat) := or ((Peano.le x0 (NUMERAL (BIT1 0))) /\ (Peano.le (NUMERAL (BIT1 0)) x0)).
Definition term16 (x0 : Prop) (x1 : Prop) (x2 : Prop -> Prop) (x3 : Prop) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term181 (x0 : nat) := False /\ (Peano.le (NUMERAL (BIT1 0)) x0).
Definition term163 (x0 : nat) (x1 : nat) := fun y0 : Prop => ((y0 \/ (Peano.le x1 x0)) /\ (y0 \/ (Peano.le x0 x1))) = (y0 \/ ((Peano.le x1 x0) /\ (Peano.le x0 x1))).
Definition term28 (x0 : nat) := imp (x0 = (NUMERAL 0)).
Definition term147 (x0 : nat) (x1 : nat) (x2 : nat) := ((False /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.le x2 x1)) /\ ((False /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.le x1 x2)).
Definition term142 (x0 : nat) (x1 : nat) (x2 : nat) := ((True /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.le x2 x1)) /\ ((True /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.le x1 x2)).
Definition term164 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => ((y0 \/ (Peano.le x1 x0)) /\ (y0 \/ (Peano.le x0 x1))) = (y0 \/ ((Peano.le x1 x0) /\ (Peano.le x0 x1)))) (Peano.le (NUMERAL (BIT1 0)) x2).
Definition term50 (x0 : nat) := or (x0 = (NUMERAL (BIT1 0))).
Definition term172 (x0 : nat) (x1 : nat) := False \/ ((Peano.le x1 x0) /\ (Peano.le x0 x1)).
Definition term112 (x0 : nat) := (True -> (Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> True).
Definition term48 (x0 : nat) (x1 : nat) := @COND Prop True ((x0 = (NUMERAL 0)) -> x1 = (NUMERAL 0)).
Definition term156 (x0 : nat) (x1 : nat) (x2 : nat) := and ((Peano.le (NUMERAL (BIT1 0)) x0) \/ (Peano.le x1 x2)).
Definition term109 (x0 : nat) := fun y0 : Prop => ((y0 -> (Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> y0)) = (y0 = ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0))).
Definition term55 (x0 : nat) (x1 : nat) (x2 : nat) := and (Peano.le (Nat.pow x1 x0) (Nat.pow x1 x2)).
Definition term10 (x0 : nat) (x1 : nat) := (fun y0 : nat => (x0 = y0) = ((Peano.le x0 y0) /\ (Peano.le y0 x0))) x1.
Definition term56 (x0 : nat) (x1 : nat) := and ((x0 = (NUMERAL 0)) -> x1 = (NUMERAL 0)).
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => ((Peano.le (Nat.pow x1 x2) (Nat.pow x1 x0)) /\ (Peano.le (Nat.pow x1 x0) (Nat.pow x1 x2))) = y0) (@COND Prop x3 x4 x5).
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 x2).
Definition term54 (x0 : nat) (x1 : nat) := @COND Prop True ((x0 = (NUMERAL 0)) -> x1 = (NUMERAL 0)) (((NUMERAL 0) = (NUMERAL (BIT1 0))) \/ (Peano.le x0 x1)).
Definition term168 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : Prop => ((y0 \/ (Peano.le x1 x0)) /\ (y0 \/ (Peano.le x0 x1))) = (y0 \/ ((Peano.le x1 x0) /\ (Peano.le x0 x1)))) (Peano.le (NUMERAL (BIT1 0)) x2)).
Definition term188 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.pow y0 y1) = (Nat.pow y0 y2)) = (@COND Prop (y0 = (NUMERAL 0)) ((y1 = (NUMERAL 0)) = (y2 = (NUMERAL 0))) ((y0 = (NUMERAL (BIT1 0))) \/ (y1 = y2))).
Definition term187 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.pow x0 y0) = (Nat.pow x0 y1)) = (@COND Prop (x0 = (NUMERAL 0)) ((y0 = (NUMERAL 0)) = (y1 = (NUMERAL 0))) ((x0 = (NUMERAL (BIT1 0))) \/ (y0 = y1))).
Definition term38 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.pow x0 y0) (Nat.pow x0 y1)) = (@COND Prop (x0 = (NUMERAL 0)) ((y0 = (NUMERAL 0)) -> y1 = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le y0 y1))).
Definition term8 := forall y0 : nat, forall y1 : nat, (y0 = y1) = ((Peano.le y0 y1) /\ (Peano.le y1 y0)).
Definition term7 := forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1).
Definition term175 (x0 : nat) (x1 : nat) := @eq Prop ((True \/ (Peano.le x1 x0)) /\ (True \/ (Peano.le x0 x1))).
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (((Peano.le (Nat.pow x0 x1) (Nat.pow x0 x2)) /\ (Peano.le (Nat.pow x0 x2) (Nat.pow x0 x1))) = (@COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) = (x2 = (NUMERAL 0))) ((x0 = (NUMERAL (BIT1 0))) \/ (x1 = x2)))).
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) -> ((Peano.le (Nat.pow x0 x1) (Nat.pow x0 x2)) /\ (Peano.le (Nat.pow x0 x2) (Nat.pow x0 x1))) = ((x0 = (NUMERAL (BIT1 0))) \/ (x1 = x2)).
Definition term177 (x0 : nat) (x1 : nat) := and (False \/ (Peano.le x0 x1)).
Definition term152 (x0 : nat) := or (Peano.le (NUMERAL (BIT1 0)) x0).
Definition term43 (x0 : nat) (x1 : nat) (x2 : nat) := @COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) -> x2 = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 x2)).
Definition term114 (x0 : nat) (x1 : nat) := @eq Prop ((((Peano.le (NUMERAL 0) x0) -> (Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)) /\ (((Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)) -> Peano.le (NUMERAL 0) x0)) = ((Peano.le (NUMERAL 0) x0) = ((Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)))).
Definition term88 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : Prop => (((y0 /\ (Peano.le (NUMERAL 0) x1)) -> (Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> y0 /\ (Peano.le (NUMERAL 0) x1))) = ((y0 /\ (Peano.le (NUMERAL 0) x1)) = ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)))) (Peano.le x1 (NUMERAL 0))).
Definition term176 (x0 : nat) (x1 : nat) := False \/ (Peano.le x0 x1).
Definition term75 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x0 (NUMERAL (BIT1 0))) /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.le x1 x2).
Definition term124 (x0 : nat) := and (False -> (Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)).
Definition term93 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => ((Peano.le (Nat.pow x0 x1) (Nat.pow x0 x2)) /\ (Peano.le (Nat.pow x0 x2) (Nat.pow x0 x1))) = y0) ((x0 = (NUMERAL (BIT1 0))) \/ (x1 = x2)).
Definition term106 (x0 : nat) := @eq Prop (Peano.le (NUMERAL 0) x0).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) -> (fun y0 : Prop => ((Peano.le (Nat.pow x0 x1) (Nat.pow x0 x2)) /\ (Peano.le (Nat.pow x0 x2) (Nat.pow x0 x1))) = y0) ((x1 = (NUMERAL 0)) = (x2 = (NUMERAL 0))).
Definition term120 (x0 : nat) := ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> True.
Definition term32 (x0 : nat) (x1 : nat) (x2 : nat) := and ((x0 = (NUMERAL 0)) -> ((Peano.le (Nat.pow x0 x1) (Nat.pow x0 x2)) /\ (Peano.le (Nat.pow x0 x2) (Nat.pow x0 x1))) = ((x1 = (NUMERAL 0)) = (x2 = (NUMERAL 0)))).
Definition term161 (x0 : nat) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) (Peano.le (NUMERAL (BIT1 0)) x0).
Definition term89 (x0 : nat) (x1 : nat) := @eq Prop (((((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> (Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)) /\ (((Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)) -> (Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0))) = (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) = ((Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)))).
Definition term46 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) -> x1 = (NUMERAL 0).
Definition term140 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => (((y0 /\ (Peano.le (NUMERAL (BIT1 0)) x2)) \/ (Peano.le x1 x0)) /\ ((y0 /\ (Peano.le (NUMERAL (BIT1 0)) x2)) \/ (Peano.le x0 x1))) = ((y0 /\ (Peano.le (NUMERAL (BIT1 0)) x2)) \/ ((Peano.le x1 x0) /\ (Peano.le x0 x1)))) (Peano.le x2 (NUMERAL (BIT1 0))).
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : Prop => ((Peano.le (Nat.pow x1 x2) (Nat.pow x1 x0)) /\ (Peano.le (Nat.pow x1 x0) (Nat.pow x1 x2))) = y0.
Definition term67 (x0 : nat) (x1 : nat) := ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> (Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1).
Definition term141 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => (((y0 /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.le x2 x1)) /\ ((y0 /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.le x1 x2))) = ((y0 /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ ((Peano.le x2 x1) /\ (Peano.le x1 x2)))) True.
Definition term173 (x0 : nat) (x1 : nat) := True \/ (Peano.le x0 x1).
Definition term83 (x0 : nat) (x1 : nat) := fun y0 : Prop => (((y0 /\ (Peano.le (NUMERAL 0) x0)) -> (Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)) /\ (((Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)) -> y0 /\ (Peano.le (NUMERAL 0) x0))) = ((y0 /\ (Peano.le (NUMERAL 0) x0)) = ((Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1))).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => ((Peano.le (Nat.pow x0 x1) (Nat.pow x0 x2)) /\ (Peano.le (Nat.pow x0 x2) (Nat.pow x0 x1))) = y0) ((x1 = (NUMERAL 0)) = (x2 = (NUMERAL 0))).
Definition term61 (x0 : nat) (x1 : nat) (x2 : nat) := @COND Prop False ((x1 = (NUMERAL 0)) -> x2 = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 x2)).
Definition term96 (x0 : nat) (x1 : nat) := (True /\ (Peano.le (NUMERAL 0) x0)) -> (Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1).
Definition term99 (x0 : nat) (x1 : nat) := and ((Peano.le (NUMERAL 0) x0) -> (Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)).
Definition term183 (x0 : nat) (x1 : nat) (x2 : nat) := (False /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.le x1 x2).
Definition term91 (x0 : nat) (x1 : nat) := ((False /\ (Peano.le (NUMERAL 0) x1)) -> (Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> False /\ (Peano.le (NUMERAL 0) x1)).
Definition term123 (x0 : nat) := False -> (Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0).
Definition term148 (x0 : nat) (x1 : nat) (x2 : nat) := (False /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ ((Peano.le x2 x1) /\ (Peano.le x1 x2)).
Definition term170 (x0 : nat) (x1 : nat) := (fun y0 : Prop => ((y0 \/ (Peano.le x1 x0)) /\ (y0 \/ (Peano.le x0 x1))) = (y0 \/ ((Peano.le x1 x0) /\ (Peano.le x0 x1)))) False.
Definition term66 (x0 : nat) := imp ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)).
Definition term41 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.pow x0 x1) (Nat.pow x0 y0)) = (@COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) -> y0 = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 y0)))) x2.
Definition term139 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : Prop => (((y0 /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.le x2 x1)) /\ ((y0 /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.le x1 x2))) = ((y0 /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ ((Peano.le x2 x1) /\ (Peano.le x1 x2))).
Definition term117 (x0 : nat) := True -> (Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0).
Definition term180 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.le x1 x0) /\ (Peano.le x0 x1)).
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = (NUMERAL 0)) -> (fun y0 : Prop => ((Peano.le (Nat.pow x0 x1) (Nat.pow x0 x2)) /\ (Peano.le (Nat.pow x0 x2) (Nat.pow x0 x1))) = y0) ((x1 = (NUMERAL 0)) = (x2 = (NUMERAL 0)))) /\ ((~ (x0 = (NUMERAL 0))) -> (fun y0 : Prop => ((Peano.le (Nat.pow x0 x1) (Nat.pow x0 x2)) /\ (Peano.le (Nat.pow x0 x2) (Nat.pow x0 x1))) = y0) ((x0 = (NUMERAL (BIT1 0))) \/ (x1 = x2))).
Definition term185 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (((False /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.le x2 x1)) /\ ((False /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.le x1 x2))).
Definition term158 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (((True /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.le x2 x1)) /\ ((True /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.le x1 x2))).
Definition term78 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((((Peano.le x0 (NUMERAL (BIT1 0))) /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.le x2 x1)) /\ (((Peano.le x0 (NUMERAL (BIT1 0))) /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.le x1 x2))).
Definition term64 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x2 x1)) /\ ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 x2))).
Definition term9 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (y0 = y1) = ((Peano.le y0 y1) /\ (Peano.le y1 y0))) x0.
Definition term80 (x0 : nat) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) (Peano.le x0 (NUMERAL 0)).
Definition term167 (x0 : nat) (x1 : nat) := True \/ ((Peano.le x1 x0) /\ (Peano.le x0 x1)).
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.pow x1 x2) (Nat.pow x1 x0)) /\ (Peano.le (Nat.pow x1 x0) (Nat.pow x1 x2)).
Definition term143 (x0 : nat) (x1 : nat) (x2 : nat) := (True /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ ((Peano.le x2 x1) /\ (Peano.le x1 x2)).
Definition term128 (x0 : nat) := @eq Prop ((False -> (Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> False)).
Definition term136 (x0 : nat) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) (Peano.le x0 (NUMERAL (BIT1 0))).
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Nat.pow x1 x0) = (Nat.pow x1 x2)).
Definition term60 (x0 : nat) (x1 : nat) := @COND Prop False ((x0 = (NUMERAL 0)) -> x1 = (NUMERAL 0)).
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) := @COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) = (x2 = (NUMERAL 0))) ((x0 = (NUMERAL (BIT1 0))) \/ (x1 = x2)).
Definition term144 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : Prop => (((y0 /\ (Peano.le (NUMERAL (BIT1 0)) x2)) \/ (Peano.le x1 x0)) /\ ((y0 /\ (Peano.le (NUMERAL (BIT1 0)) x2)) \/ (Peano.le x0 x1))) = ((y0 /\ (Peano.le (NUMERAL (BIT1 0)) x2)) \/ ((Peano.le x1 x0) /\ (Peano.le x0 x1)))) (Peano.le x2 (NUMERAL (BIT1 0)))).
Definition term4 (x0 : nat) := forall y0 : nat, (x0 = y0) = ((Peano.le x0 y0) /\ (Peano.le y0 x0)).
Definition term162 (x0 : nat) := ((Peano.le (NUMERAL (BIT1 0)) x0) = True) \/ ((Peano.le (NUMERAL (BIT1 0)) x0) = False).
Definition term108 (x0 : nat) := ((Peano.le (NUMERAL 0) x0) = True) \/ ((Peano.le (NUMERAL 0) x0) = False).
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL (BIT1 0))) \/ (x1 = x2).
Definition term86 (x0 : nat) (x1 : nat) := ((True /\ (Peano.le (NUMERAL 0) x1)) -> (Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> True /\ (Peano.le (NUMERAL 0) x1)).
Definition term95 (x0 : nat) := imp (Peano.le (NUMERAL 0) x0).
Definition term184 (x0 : nat) (x1 : nat) (x2 : nat) := and ((False /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.le x1 x2)).
Definition term155 (x0 : nat) (x1 : nat) (x2 : nat) := and ((True /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.le x1 x2)).
Definition term110 (x0 : nat) (x1 : nat) := (fun y0 : Prop => ((y0 -> (Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> y0)) = (y0 = ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)))) (Peano.le (NUMERAL 0) x1).
Definition term157 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le (NUMERAL (BIT1 0)) x0) \/ (Peano.le x2 x1)) /\ ((Peano.le (NUMERAL (BIT1 0)) x0) \/ (Peano.le x1 x2)).
Definition term59 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term97 (x0 : nat) (x1 : nat) := (Peano.le (NUMERAL 0) x0) -> (Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1).
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => ((Peano.le (Nat.pow x0 x1) (Nat.pow x0 x2)) /\ (Peano.le (Nat.pow x0 x2) (Nat.pow x0 x1))) = y0) (@COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) = (x2 = (NUMERAL 0))) ((x0 = (NUMERAL (BIT1 0))) \/ (x1 = x2))).
Definition term116 (x0 : nat) := (False -> (Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> False).
Definition term100 (x0 : nat) (x1 : nat) := ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> True /\ (Peano.le (NUMERAL 0) x1).
Definition term63 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x2 x1)) /\ ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 x2)).
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Peano.le (Nat.pow x1 x2) (Nat.pow x1 x0)) /\ (Peano.le (Nat.pow x1 x0) (Nat.pow x1 x2))).
Definition term129 (x0 : nat) := @eq Prop (~ ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0))).
Definition term113 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : Prop => ((y0 -> (Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> y0)) = (y0 = ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)))) (Peano.le (NUMERAL 0) x1)).
Definition term73 (x0 : nat) := (Peano.le x0 (NUMERAL (BIT1 0))) /\ (Peano.le (NUMERAL (BIT1 0)) x0).
Definition term84 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (((y0 /\ (Peano.le (NUMERAL 0) x1)) -> (Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> y0 /\ (Peano.le (NUMERAL 0) x1))) = ((y0 /\ (Peano.le (NUMERAL 0) x1)) = ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)))) (Peano.le x1 (NUMERAL 0)).
Definition term90 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (((y0 /\ (Peano.le (NUMERAL 0) x0)) -> (Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)) /\ (((Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)) -> y0 /\ (Peano.le (NUMERAL 0) x0))) = ((y0 /\ (Peano.le (NUMERAL 0) x0)) = ((Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)))) False.
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.pow x1 x0) (Nat.pow x1 x2).
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) -> (fun y0 : Prop => ((Peano.le (Nat.pow x0 x1) (Nat.pow x0 x2)) /\ (Peano.le (Nat.pow x0 x2) (Nat.pow x0 x1))) = y0) ((x0 = (NUMERAL (BIT1 0))) \/ (x1 = x2)).
Definition term165 (x0 : nat) (x1 : nat) := (fun y0 : Prop => ((y0 \/ (Peano.le x1 x0)) /\ (y0 \/ (Peano.le x0 x1))) = (y0 \/ ((Peano.le x1 x0) /\ (Peano.le x0 x1)))) True.
Definition term62 (x0 : nat) (x1 : nat) (x2 : nat) := and ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 x2)).
Definition term15 (x0 : Prop -> Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := x0 (@COND Prop x1 x2 x3).
Definition term87 (x0 : nat) := True /\ (Peano.le (NUMERAL 0) x0).
Definition term169 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((((Peano.le (NUMERAL (BIT1 0)) x0) \/ (Peano.le x2 x1)) /\ ((Peano.le (NUMERAL (BIT1 0)) x0) \/ (Peano.le x1 x2))) = ((Peano.le (NUMERAL (BIT1 0)) x0) \/ ((Peano.le x2 x1) /\ (Peano.le x1 x2)))).
Definition term81 (x0 : nat) := Peano.le x0 (NUMERAL 0).
Definition term145 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (((((Peano.le x0 (NUMERAL (BIT1 0))) /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.le x2 x1)) /\ (((Peano.le x0 (NUMERAL (BIT1 0))) /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.le x1 x2))) = (((Peano.le x0 (NUMERAL (BIT1 0))) /\ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ ((Peano.le x2 x1) /\ (Peano.le x1 x2)))).
Definition term186 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.pow x0 x1) = (Nat.pow x0 y0)) = (@COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) = (y0 = (NUMERAL 0))) ((x0 = (NUMERAL (BIT1 0))) \/ (x1 = y0))).
Definition term40 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.pow x0 x1) (Nat.pow x0 y0)) = (@COND Prop (x0 = (NUMERAL 0)) ((x1 = (NUMERAL 0)) -> y0 = (NUMERAL 0)) ((x0 = (NUMERAL (BIT1 0))) \/ (Peano.le x1 y0))).
Definition term137 (x0 : nat) := Peano.le x0 (NUMERAL (BIT1 0)).
Definition term166 (x0 : nat) (x1 : nat) := (True \/ (Peano.le x1 x0)) /\ (True \/ (Peano.le x0 x1)).
Definition term71 (x0 : nat) := @eq Prop (x0 = (NUMERAL 0)).
Definition term6 := fun y0 : nat => forall y1 : nat, (y0 = y1) = ((Peano.le y0 y1) /\ (Peano.le y1 y0)).
Definition term178 (x0 : nat) (x1 : nat) := and (Peano.le x0 x1).
Definition term138 (x0 : nat) := ((Peano.le x0 (NUMERAL (BIT1 0))) = True) \/ ((Peano.le x0 (NUMERAL (BIT1 0))) = False).
Definition term82 (x0 : nat) := ((Peano.le x0 (NUMERAL 0)) = True) \/ ((Peano.le x0 (NUMERAL 0)) = False).
Definition term49 := NUMERAL (BIT1 0).
Definition term70 (x0 : nat) (x1 : nat) := @eq Prop ((((Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)) -> (Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> (Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1))).
Definition term111 (x0 : nat) := (fun y0 : Prop => ((y0 -> (Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> y0)) = (y0 = ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)))) True.
Definition term159 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (((Peano.le (NUMERAL (BIT1 0)) x0) \/ (Peano.le x2 x1)) /\ ((Peano.le (NUMERAL (BIT1 0)) x0) \/ (Peano.le x1 x2))).
Definition term68 (x0 : nat) (x1 : nat) := and (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) -> (Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)).
