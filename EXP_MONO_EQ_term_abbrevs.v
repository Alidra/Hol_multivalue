Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term105 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) \/ (False /\ (Peano.le (NUMERAL 0) x2)).
Definition term81 (x0 : nat) (x1 : nat) (x2 : nat) := (False /\ (Peano.le (NUMERAL 0) x2)) /\ ((Peano.le x0 x1) \/ (False /\ (Peano.le (NUMERAL 0) x2))).
Definition term64 (x0 : nat) := and ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)).
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2)).
Definition term9 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.pow y0 y2) (Nat.pow y1 y2)) = ((Peano.le y0 y1) \/ (y2 = (NUMERAL 0)))) x0.
Definition term0 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) /\ (Peano.le x0 x1).
Definition term97 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : Prop => (y0 /\ ((Peano.le x0 x1) \/ y0)) = y0) (Peano.le (NUMERAL 0) x2)).
Definition term43 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) (Peano.le x0 x1).
Definition term1 (x0 : nat) := fun y0 : nat => ((Peano.le x0 y0) /\ (Peano.le y0 x0)) = (x0 = y0).
Definition term3 (x0 : nat) := forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x0)) = (x0 = y0).
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0)) = ((Peano.le x0 x1) \/ (y0 = (NUMERAL 0)))) x2.
Definition term19 (x0 : nat) := (Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0).
Definition term66 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((False \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2))) /\ ((Peano.le x0 x1) \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2)))).
Definition term58 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((True \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2))) /\ ((Peano.le x0 x1) \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2)))).
Definition term28 (x0 : nat) (x1 : nat) := or ((Peano.le x1 x0) /\ (Peano.le x0 x1)).
Definition term65 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2)) /\ ((Peano.le x0 x1) \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2))).
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : Prop => ((y0 \/ ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0))) /\ ((Peano.le x2 x1) \/ ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)))) = ((y0 /\ (Peano.le x2 x1)) \/ ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)))) (Peano.le x1 x2)).
Definition term82 (x0 : nat) := False /\ (Peano.le (NUMERAL 0) x0).
Definition term55 (x0 : nat) := True \/ ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)).
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2).
Definition term99 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (y0 /\ ((Peano.le x0 x1) \/ y0)) = y0) False.
Definition term2 (x0 : nat) := fun y0 : nat => (x0 = y0) = ((Peano.le x0 y0) /\ (Peano.le y0 x0)).
Definition term101 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) \/ True.
Definition term90 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Peano.le (NUMERAL 0) x2) /\ ((Peano.le x0 x1) \/ (Peano.le (NUMERAL 0) x2))).
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := and ((Peano.le x0 x1) \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2))).
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => ((y0 \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2))) /\ ((Peano.le x0 x1) \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2)))) = ((y0 /\ (Peano.le x0 x1)) \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2)))) False.
Definition term91 (x0 : nat) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) (Peano.le (NUMERAL 0) x0).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x1) \/ (x2 = (NUMERAL 0)).
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) := (False \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2))) /\ ((Peano.le x0 x1) \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2))).
Definition term34 (x0 : nat) (x1 : nat) := forall y0 : nat, (((Peano.le x1 x0) \/ ((Peano.le y0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0))) /\ ((Peano.le x0 x1) \/ ((Peano.le y0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)))) = (((Peano.le x1 x0) /\ (Peano.le x0 x1)) \/ ((Peano.le y0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0))).
Definition term33 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.pow x0 y0) = (Nat.pow x1 y0)) = ((x0 = x1) \/ (y0 = (NUMERAL 0))).
Definition term12 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.pow x0 y0) (Nat.pow x1 y0)) = ((Peano.le x0 x1) \/ (y0 = (NUMERAL 0))).
Definition term11 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.pow x0 y1) (Nat.pow y0 y1)) = ((Peano.le x0 y0) \/ (y1 = (NUMERAL 0)))) x1.
Definition term85 (x0 : nat) := and (Peano.le (NUMERAL 0) x0).
Definition term46 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => ((y0 \/ ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0))) /\ ((Peano.le x2 x1) \/ ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)))) = ((y0 /\ (Peano.le x2 x1)) \/ ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)))) (Peano.le x1 x2).
Definition term5 := fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1).
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) := and (Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2)).
Definition term80 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => ((y0 /\ (Peano.le (NUMERAL 0) x2)) /\ ((Peano.le x0 x1) \/ (y0 /\ (Peano.le (NUMERAL 0) x2)))) = (y0 /\ (Peano.le (NUMERAL 0) x2))) False.
Definition term20 (x0 : nat) (x1 : nat) := or (Peano.le x0 x1).
Definition term54 (x0 : nat) (x1 : nat) (x2 : nat) := (False /\ (Peano.le x0 x1)) \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2)).
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (((Peano.le x1 x0) \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2))) /\ ((Peano.le x0 x1) \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2)))).
Definition term57 (x0 : nat) (x1 : nat) (x2 : nat) := True /\ ((Peano.le x0 x1) \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2))).
Definition term17 (x0 : nat) (x1 : nat) := (fun y0 : nat => (x0 = y0) = ((Peano.le x0 y0) /\ (Peano.le y0 x0))) x1.
Definition term94 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => (y0 /\ ((Peano.le x0 x1) \/ y0)) = y0) (Peano.le (NUMERAL 0) x2).
Definition term100 (x0 : nat) (x1 : nat) := False /\ ((Peano.le x0 x1) \/ False).
Definition term42 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (((Peano.le y0 y1) \/ ((Peano.le y2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y2))) /\ ((Peano.le y1 y0) \/ ((Peano.le y2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y2)))) = (((Peano.le y0 y1) /\ (Peano.le y1 y0)) \/ ((Peano.le y2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y2))).
Definition term41 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Nat.pow y0 y2) = (Nat.pow y1 y2)) = ((y0 = y1) \/ (y2 = (NUMERAL 0))).
Definition term38 (x0 : nat) := forall y0 : nat, forall y1 : nat, (((Peano.le x0 y0) \/ ((Peano.le y1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1))) /\ ((Peano.le y0 x0) \/ ((Peano.le y1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)))) = (((Peano.le x0 y0) /\ (Peano.le y0 x0)) \/ ((Peano.le y1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1))).
Definition term37 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.pow x0 y1) = (Nat.pow y0 y1)) = ((x0 = y0) \/ (y1 = (NUMERAL 0))).
Definition term10 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.pow x0 y1) (Nat.pow y0 y1)) = ((Peano.le x0 y0) \/ (y1 = (NUMERAL 0))).
Definition term8 := forall y0 : nat, forall y1 : nat, (y0 = y1) = ((Peano.le y0 y1) /\ (Peano.le y1 y0)).
Definition term7 := forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1).
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x1)) \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2)).
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.pow x1 x2) (Nat.pow x0 x2)) /\ (Peano.le (Nat.pow x0 x2) (Nat.pow x1 x2)).
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat) := (True \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2))) /\ ((Peano.le x0 x1) \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2))).
Definition term104 (x0 : nat) := and (False /\ (Peano.le (NUMERAL 0) x0)).
Definition term69 (x0 : nat) (x1 : nat) := or (False /\ (Peano.le x0 x1)).
Definition term88 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (NUMERAL 0) x2) /\ ((Peano.le x0 x1) \/ (Peano.le (NUMERAL 0) x2)).
Definition term102 (x0 : nat) (x1 : nat) := ~ (False /\ ((Peano.le x0 x1) \/ False)).
Definition term62 (x0 : nat) := False \/ ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)).
Definition term96 (x0 : nat) (x1 : nat) := True /\ ((Peano.le x0 x1) \/ True).
Definition term45 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : Prop => ((y0 \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2))) /\ ((Peano.le x0 x1) \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2)))) = ((y0 /\ (Peano.le x0 x1)) \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2))).
Definition term83 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term106 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((False /\ (Peano.le (NUMERAL 0) x2)) /\ ((Peano.le x0 x1) \/ (False /\ (Peano.le (NUMERAL 0) x2)))).
Definition term89 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((True /\ (Peano.le (NUMERAL 0) x2)) /\ ((Peano.le x0 x1) \/ (True /\ (Peano.le (NUMERAL 0) x2)))).
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Nat.pow x0 x2) = (Nat.pow x1 x2)).
Definition term93 (x0 : nat) (x1 : nat) := fun y0 : Prop => (y0 /\ ((Peano.le x0 x1) \/ y0)) = y0.
Definition term56 (x0 : nat) := and (True \/ ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0))).
Definition term79 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2)) /\ ((Peano.le x0 x1) \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2)))) = ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2))).
Definition term47 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => ((y0 \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2))) /\ ((Peano.le x0 x1) \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2)))) = ((y0 /\ (Peano.le x0 x1)) \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2)))) True.
Definition term73 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : Prop => ((y0 /\ (Peano.le (NUMERAL 0) x2)) /\ ((Peano.le x0 x1) \/ (y0 /\ (Peano.le (NUMERAL 0) x2)))) = (y0 /\ (Peano.le (NUMERAL 0) x2)).
Definition term75 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => ((y0 /\ (Peano.le (NUMERAL 0) x2)) /\ ((Peano.le x0 x1) \/ (y0 /\ (Peano.le (NUMERAL 0) x2)))) = (y0 /\ (Peano.le (NUMERAL 0) x2))) True.
Definition term78 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : Prop => ((y0 /\ (Peano.le (NUMERAL 0) x2)) /\ ((Peano.le x0 x1) \/ (y0 /\ (Peano.le (NUMERAL 0) x2)))) = (y0 /\ (Peano.le (NUMERAL 0) x2))) (Peano.le x2 (NUMERAL 0))).
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat) := (True /\ (Peano.le (NUMERAL 0) x2)) /\ ((Peano.le x0 x1) \/ (True /\ (Peano.le (NUMERAL 0) x2))).
Definition term59 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Peano.le x0 x1) \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2))).
Definition term16 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (y0 = y1) = ((Peano.le y0 y1) /\ (Peano.le y1 y0))) x0.
Definition term70 (x0 : nat) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) (Peano.le x0 (NUMERAL 0)).
Definition term87 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) \/ (Peano.le (NUMERAL 0) x2).
Definition term68 (x0 : nat) (x1 : nat) := False /\ (Peano.le x0 x1).
Definition term4 (x0 : nat) := forall y0 : nat, (x0 = y0) = ((Peano.le x0 y0) /\ (Peano.le y0 x0)).
Definition term92 (x0 : nat) := ((Peano.le (NUMERAL 0) x0) = True) \/ ((Peano.le (NUMERAL 0) x0) = False).
Definition term44 (x0 : nat) (x1 : nat) := ((Peano.le x0 x1) = True) \/ ((Peano.le x0 x1) = False).
Definition term60 (x0 : nat) (x1 : nat) := True /\ (Peano.le x0 x1).
Definition term61 (x0 : nat) (x1 : nat) := or (True /\ (Peano.le x0 x1)).
Definition term98 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (((Peano.le (NUMERAL 0) x2) /\ ((Peano.le x0 x1) \/ (Peano.le (NUMERAL 0) x2))) = (Peano.le (NUMERAL 0) x2)).
Definition term103 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) \/ False.
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2))) /\ ((Peano.le x0 x1) \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2))).
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) \/ (x2 = (NUMERAL 0)).
Definition term86 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) \/ (True /\ (Peano.le (NUMERAL 0) x2)).
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : Prop => ((y0 /\ (Peano.le (NUMERAL 0) x2)) /\ ((Peano.le x0 x1) \/ (y0 /\ (Peano.le (NUMERAL 0) x2)))) = (y0 /\ (Peano.le (NUMERAL 0) x2))) (Peano.le x2 (NUMERAL 0)).
Definition term95 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (y0 /\ ((Peano.le x0 x1) \/ y0)) = y0) True.
Definition term84 (x0 : nat) := and (True /\ (Peano.le (NUMERAL 0) x0)).
Definition term77 (x0 : nat) := True /\ (Peano.le (NUMERAL 0) x0).
Definition term31 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Nat.pow x0 y0) = (Nat.pow x1 y0)) = ((x0 = x1) \/ (y0 = (NUMERAL 0))).
Definition term71 (x0 : nat) := Peano.le x0 (NUMERAL 0).
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((((Peano.le x1 x0) \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2))) /\ ((Peano.le x0 x1) \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2)))) = (((Peano.le x1 x0) /\ (Peano.le x0 x1)) \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2)))).
Definition term49 (x0 : nat) (x1 : nat) (x2 : nat) := (True /\ (Peano.le x0 x1)) \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2)).
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2)) /\ ((Peano.le x0 x1) \/ ((Peano.le x2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x2)))).
Definition term27 (x0 : nat) (x1 : nat) := or (x0 = x1).
Definition term36 (x0 : nat) := fun y0 : nat => forall y1 : nat, (((Peano.le x0 y0) \/ ((Peano.le y1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1))) /\ ((Peano.le y0 x0) \/ ((Peano.le y1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1)))) = (((Peano.le x0 y0) /\ (Peano.le y0 x0)) \/ ((Peano.le y1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y1))).
Definition term35 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((Nat.pow x0 y1) = (Nat.pow y0 y1)) = ((x0 = y0) \/ (y1 = (NUMERAL 0))).
Definition term6 := fun y0 : nat => forall y1 : nat, (y0 = y1) = ((Peano.le y0 y1) /\ (Peano.le y1 y0)).
Definition term72 (x0 : nat) := ((Peano.le x0 (NUMERAL 0)) = True) \/ ((Peano.le x0 (NUMERAL 0)) = False).
Definition term63 (x0 : nat) := and (False \/ ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0))).
Definition term40 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (((Peano.le y0 y1) \/ ((Peano.le y2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y2))) /\ ((Peano.le y1 y0) \/ ((Peano.le y2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y2)))) = (((Peano.le y0 y1) /\ (Peano.le y1 y0)) \/ ((Peano.le y2 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y2))).
Definition term39 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.pow y0 y2) = (Nat.pow y1 y2)) = ((y0 = y1) \/ (y2 = (NUMERAL 0))).
Definition term32 (x0 : nat) (x1 : nat) := fun y0 : nat => (((Peano.le x1 x0) \/ ((Peano.le y0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0))) /\ ((Peano.le x0 x1) \/ ((Peano.le y0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0)))) = (((Peano.le x1 x0) /\ (Peano.le x0 x1)) \/ ((Peano.le y0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) y0))).
