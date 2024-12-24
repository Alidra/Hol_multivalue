Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term49 (x0 : nat) (x1 : nat) := @eq Prop ((real_of_num x0) = (real_neg (real_of_num x1))).
Definition term17 (x0 : real) := forall y0 : real, ((real_le x0 y0) /\ (real_le y0 x0)) = (x0 = y0).
Definition term16 (x0 : real) := fun y0 : real => (x0 = y0) = ((real_le x0 y0) /\ (real_le y0 x0)).
Definition term36 (x0 : nat) (x1 : nat) := and (((real_neg (real_of_num x0)) = (real_neg (real_of_num x1))) = (x0 = x1)).
Definition term43 (x0 : nat) := and ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)).
Definition term3 (x0 : nat) := (fun y0 : nat => (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) x0.
Definition term52 (x0 : nat) (x1 : nat) := (((real_le (real_neg (real_of_num x0)) (real_of_num x1)) /\ (real_le (real_of_num x1) (real_neg (real_of_num x0)))) = (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ ((Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)))) /\ (((real_le (real_of_num x0) (real_neg (real_of_num x1))) /\ (real_le (real_neg (real_of_num x1)) (real_of_num x0))) = (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ ((Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)))).
Definition term32 (x0 : nat) := real_neg (real_of_num x0).
Definition term5 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) /\ (Peano.le x0 x1).
Definition term50 (x0 : nat) (x1 : nat) := @eq Prop ((real_le (real_of_num x1) (real_neg (real_of_num x0))) /\ (real_le (real_neg (real_of_num x0)) (real_of_num x1))).
Definition term34 (x0 : nat) (x1 : nat) := @eq Prop ((real_neg (real_of_num x0)) = (real_neg (real_of_num x1))).
Definition term75 (x0 : nat) (x1 : nat) := (((x1 = (NUMERAL 0)) /\ (x0 = (NUMERAL 0))) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))) /\ True.
Definition term38 (x0 : nat) (x1 : nat) := (real_le (real_neg (real_of_num x1)) (real_of_num x0)) /\ (real_le (real_of_num x0) (real_neg (real_of_num x1))).
Definition term102 (x0 : nat) := False /\ (x0 = (NUMERAL 0)).
Definition term47 (x0 : nat) (x1 : nat) := and (((real_le (real_neg (real_of_num x0)) (real_of_num x1)) /\ (real_le (real_of_num x1) (real_neg (real_of_num x0)))) = (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ ((Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)))).
Definition term96 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (y0 /\ (x0 = (NUMERAL 0))) = ((x0 = (NUMERAL 0)) /\ y0)) (x1 = (NUMERAL 0)).
Definition term39 (x0 : nat) (x1 : nat) := @eq Prop ((real_neg (real_of_num x0)) = (real_of_num x1)).
Definition term61 (x0 : nat) (x1 : nat) := real_le (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term78 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) (Peano.le x0 x1).
Definition term6 (x0 : nat) := fun y0 : nat => ((Peano.le x0 y0) /\ (Peano.le y0 x0)) = (x0 = y0).
Definition term8 (x0 : nat) := forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x0)) = (x0 = y0).
Definition term68 (x0 : nat) (x1 : nat) := @eq Prop ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0))).
Definition term33 (x0 : nat) (x1 : nat) := (real_le (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) /\ (real_le (real_neg (real_of_num x0)) (real_neg (real_of_num x1))).
Definition term66 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_neg (real_of_num x1)).
Definition term41 (x0 : nat) := (Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0).
Definition term26 (x0 : real) (x1 : real) := (fun y0 : real => (x0 = y0) = ((real_le x0 y0) /\ (real_le y0 x0))) x1.
Definition term73 (x0 : nat) (x1 : nat) := and ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0))).
Definition term0 (x0 : nat) := (fun y0 : nat => Peano.le (NUMERAL 0) y0) x0.
Definition term72 (x0 : nat) (x1 : nat) := and (real_le (real_of_num x0) (real_neg (real_of_num x1))).
Definition term27 (x0 : nat) (x1 : nat) := (real_le (real_of_num x1) (real_of_num x0)) /\ (real_le (real_of_num x0) (real_of_num x1)).
Definition term42 (x0 : nat) := and (x0 = (NUMERAL 0)).
Definition term53 (x0 : nat) (x1 : nat) := (((real_neg (real_of_num x0)) = (real_neg (real_of_num x1))) = (x0 = x1)) /\ ((((real_neg (real_of_num x0)) = (real_of_num x1)) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))) /\ (((real_of_num x0) = (real_neg (real_of_num x1))) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0))))).
Definition term7 (x0 : nat) := fun y0 : nat => (x0 = y0) = ((Peano.le x0 y0) /\ (Peano.le y0 x0)).
Definition term22 := forall y0 : real, forall y1 : real, (y0 = y1) = ((real_le y0 y1) /\ (real_le y1 y0)).
Definition term21 := forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1).
Definition term98 (x0 : nat) := True /\ (x0 = (NUMERAL 0)).
Definition term67 (x0 : nat) (x1 : nat) := True /\ ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0))).
Definition term95 (x0 : nat) := fun y0 : Prop => (y0 /\ (x0 = (NUMERAL 0))) = ((x0 = (NUMERAL 0)) /\ y0).
Definition term62 (x0 : nat) (x1 : nat) := and (real_le (real_neg (real_of_num x0)) (real_neg (real_of_num x1))).
Definition term51 (x0 : nat) (x1 : nat) := (((real_neg (real_of_num x0)) = (real_of_num x1)) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))) /\ (((real_of_num x0) = (real_neg (real_of_num x1))) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))).
Definition term106 (x0 : nat) := @eq Prop (False /\ (x0 = (NUMERAL 0))).
Definition term104 (x0 : nat) := @eq Prop (True /\ (x0 = (NUMERAL 0))).
Definition term44 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term71 (x0 : nat) (x1 : nat) := and (((x1 = (NUMERAL 0)) /\ (x0 = (NUMERAL 0))) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))).
Definition term10 := fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1).
Definition term74 (x0 : nat) (x1 : nat) := ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0))) /\ True.
Definition term99 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : Prop => (y0 /\ (x0 = (NUMERAL 0))) = ((x0 = (NUMERAL 0)) /\ y0)) (x1 = (NUMERAL 0))).
Definition term20 := fun y0 : real => forall y1 : real, (y0 = y1) = ((real_le y0 y1) /\ (real_le y1 y0)).
Definition term29 (x0 : nat) (x1 : nat) := @eq Prop ((real_le (real_of_num x1) (real_of_num x0)) /\ (real_le (real_of_num x0) (real_of_num x1))).
Definition term56 (x0 : nat) (x1 : nat) := (((real_le (real_of_num x0) (real_of_num x1)) /\ (real_le (real_of_num x1) (real_of_num x0))) = ((Peano.le x0 x1) /\ (Peano.le x1 x0))) /\ ((((real_le (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) /\ (real_le (real_neg (real_of_num x1)) (real_neg (real_of_num x0)))) = ((Peano.le x0 x1) /\ (Peano.le x1 x0))) /\ ((((real_le (real_neg (real_of_num x0)) (real_of_num x1)) /\ (real_le (real_of_num x1) (real_neg (real_of_num x0)))) = (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ ((Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)))) /\ (((real_le (real_of_num x0) (real_neg (real_of_num x1))) /\ (real_le (real_neg (real_of_num x1)) (real_of_num x0))) = (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ ((Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)))))).
Definition term14 (x0 : real) (x1 : real) := (real_le x1 x0) /\ (real_le x0 x1).
Definition term64 (x0 : nat) (x1 : nat) := real_le (real_neg (real_of_num x0)) (real_of_num x1).
Definition term70 (x0 : nat) := (x0 = (NUMERAL 0)) /\ True.
Definition term24 (x0 : nat) (x1 : nat) := (fun y0 : nat => (x0 = y0) = ((Peano.le x0 y0) /\ (Peano.le y0 x0))) x1.
Definition term30 (x0 : nat) (x1 : nat) := and (((real_of_num x0) = (real_of_num x1)) = (x0 = x1)).
Definition term54 (x0 : nat) (x1 : nat) := (((real_le (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) /\ (real_le (real_neg (real_of_num x1)) (real_neg (real_of_num x0)))) = ((Peano.le x0 x1) /\ (Peano.le x1 x0))) /\ ((((real_le (real_neg (real_of_num x0)) (real_of_num x1)) /\ (real_le (real_of_num x1) (real_neg (real_of_num x0)))) = (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ ((Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)))) /\ (((real_le (real_of_num x0) (real_neg (real_of_num x1))) /\ (real_le (real_neg (real_of_num x1)) (real_of_num x0))) = (((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ ((Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1))))).
Definition term13 := forall y0 : nat, forall y1 : nat, (y0 = y1) = ((Peano.le y0 y1) /\ (Peano.le y1 y0)).
Definition term12 := forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1).
Definition term100 (x0 : nat) (x1 : nat) := @eq Prop (((x1 = (NUMERAL 0)) /\ (x0 = (NUMERAL 0))) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))).
Definition term45 (x0 : nat) (x1 : nat) := ((Peano.le x0 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x0)) /\ ((Peano.le x1 (NUMERAL 0)) /\ (Peano.le (NUMERAL 0) x1)).
Definition term19 := fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1).
Definition term69 (x0 : nat) := and (Peano.le x0 (NUMERAL 0)).
Definition term89 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) /\ False.
Definition term25 (x0 : real) := (fun y0 : real => forall y1 : real, (y0 = y1) = ((real_le y0 y1) /\ (real_le y1 y0))) x0.
Definition term86 (x0 : nat) (x1 : nat) := @eq Prop (((Peano.le x0 x1) /\ (Peano.le x1 x0)) = ((Peano.le x1 x0) /\ (Peano.le x0 x1))).
Definition term1 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term63 (x0 : nat) (x1 : nat) := and (((Peano.le x0 x1) /\ (Peano.le x1 x0)) = ((Peano.le x1 x0) /\ (Peano.le x0 x1))).
Definition term91 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le x0 x1).
Definition term15 (x0 : real) := fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) = (x0 = y0).
Definition term28 (x0 : nat) (x1 : nat) := @eq Prop ((real_of_num x0) = (real_of_num x1)).
Definition term103 (x0 : nat) := (x0 = (NUMERAL 0)) /\ False.
Definition term35 (x0 : nat) (x1 : nat) := @eq Prop ((real_le (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) /\ (real_le (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))).
Definition term84 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) /\ True.
Definition term60 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.le x1 x0) /\ (Peano.le x0 x1)).
Definition term58 (x0 : nat) (x1 : nat) := and (real_le (real_of_num x0) (real_of_num x1)).
Definition term23 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (y0 = y1) = ((Peano.le y0 y1) /\ (Peano.le y1 y0))) x0.
Definition term88 (x0 : nat) (x1 : nat) := False /\ (Peano.le x0 x1).
Definition term46 (x0 : nat) (x1 : nat) := and (((real_neg (real_of_num x0)) = (real_of_num x1)) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))).
Definition term9 (x0 : nat) := forall y0 : nat, (x0 = y0) = ((Peano.le x0 y0) /\ (Peano.le y0 x0)).
Definition term37 (x0 : nat) (x1 : nat) := and (((real_le (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) /\ (real_le (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = ((Peano.le x1 x0) /\ (Peano.le x0 x1))).
Definition term31 (x0 : nat) (x1 : nat) := and (((real_le (real_of_num x1) (real_of_num x0)) /\ (real_le (real_of_num x0) (real_of_num x1))) = ((Peano.le x1 x0) /\ (Peano.le x0 x1))).
Definition term79 (x0 : nat) (x1 : nat) := ((Peano.le x0 x1) = True) \/ ((Peano.le x0 x1) = False).
Definition term2 := forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term83 (x0 : nat) (x1 : nat) := True /\ (Peano.le x0 x1).
Definition term101 (x0 : nat) := (fun y0 : Prop => (y0 /\ (x0 = (NUMERAL 0))) = ((x0 = (NUMERAL 0)) /\ y0)) False.
Definition term85 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : Prop => (y0 /\ (Peano.le x1 x0)) = ((Peano.le x1 x0) /\ y0)) (Peano.le x0 x1)).
Definition term93 (x0 : nat) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) (x0 = (NUMERAL 0)).
Definition term65 (x0 : nat) (x1 : nat) := and (real_le (real_neg (real_of_num x0)) (real_of_num x1)).
Definition term40 (x0 : nat) (x1 : nat) := @eq Prop ((real_le (real_neg (real_of_num x1)) (real_of_num x0)) /\ (real_le (real_of_num x0) (real_neg (real_of_num x1)))).
Definition term92 (x0 : nat) (x1 : nat) := @eq Prop (False /\ (Peano.le x0 x1)).
Definition term57 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_of_num x1).
Definition term48 (x0 : nat) (x1 : nat) := (real_le (real_of_num x1) (real_neg (real_of_num x0))) /\ (real_le (real_neg (real_of_num x0)) (real_of_num x1)).
Definition term18 (x0 : real) := forall y0 : real, (x0 = y0) = ((real_le x0 y0) /\ (real_le y0 x0)).
Definition term82 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (y0 /\ (Peano.le x0 x1)) = ((Peano.le x0 x1) /\ y0)) True.
Definition term81 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (y0 /\ (Peano.le x1 x0)) = ((Peano.le x1 x0) /\ y0)) (Peano.le x0 x1).
Definition term77 (x0 : nat) (x1 : nat) := True /\ ((((Peano.le x1 x0) /\ (Peano.le x0 x1)) = ((Peano.le x0 x1) /\ (Peano.le x1 x0))) /\ (((x1 = (NUMERAL 0)) /\ (x0 = (NUMERAL 0))) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0))))).
Definition term55 (x0 : nat) (x1 : nat) := (((real_of_num x0) = (real_of_num x1)) = (x0 = x1)) /\ ((((real_neg (real_of_num x0)) = (real_neg (real_of_num x1))) = (x0 = x1)) /\ ((((real_neg (real_of_num x0)) = (real_of_num x1)) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))) /\ (((real_of_num x0) = (real_neg (real_of_num x1))) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))))).
Definition term4 (x0 : nat) := Peano.le x0 (NUMERAL 0).
Definition term97 (x0 : nat) := (fun y0 : Prop => (y0 /\ (x0 = (NUMERAL 0))) = ((x0 = (NUMERAL 0)) /\ y0)) True.
Definition term90 (x0 : nat) (x1 : nat) := @eq Prop (True /\ (Peano.le x0 x1)).
Definition term105 (x0 : nat) := @eq Prop (x0 = (NUMERAL 0)).
Definition term11 := fun y0 : nat => forall y1 : nat, (y0 = y1) = ((Peano.le y0 y1) /\ (Peano.le y1 y0)).
Definition term59 (x0 : nat) (x1 : nat) := and (Peano.le x0 x1).
Definition term80 (x0 : nat) (x1 : nat) := fun y0 : Prop => (y0 /\ (Peano.le x0 x1)) = ((Peano.le x0 x1) /\ y0).
Definition term94 (x0 : nat) := ((x0 = (NUMERAL 0)) = True) \/ ((x0 = (NUMERAL 0)) = False).
Definition term76 (x0 : nat) (x1 : nat) := (((Peano.le x1 x0) /\ (Peano.le x0 x1)) = ((Peano.le x0 x1) /\ (Peano.le x1 x0))) /\ (((x1 = (NUMERAL 0)) /\ (x0 = (NUMERAL 0))) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))).
Definition term87 (x0 : nat) (x1 : nat) := (fun y0 : Prop => (y0 /\ (Peano.le x0 x1)) = ((Peano.le x0 x1) /\ y0)) False.
