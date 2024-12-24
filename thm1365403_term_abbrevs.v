Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term50 (x0 : nat) (x1 : nat) := @eq Prop (real_le (real_of_num x0) (real_neg (real_of_num x1))).
Definition term64 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le (Nat.add x0 x1) (NUMERAL 0)).
Definition term26 (x0 : real) (x1 : real) := real_le (real_neg x0) x1.
Definition term5 (x0 : nat) := (fun y0 : nat => (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) x0.
Definition term46 (x0 : nat) (x1 : nat) := (real_le (real_neg (real_of_num x0)) (real_of_num x1)) /\ (((real_le (real_of_num x0) (real_of_num x1)) = (Peano.le x0 x1)) /\ (((real_le (real_of_num x1) (real_of_num x0)) = (Peano.le x1 x0)) /\ ((real_le (real_of_num x0) (real_neg (real_of_num x1))) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))))).
Definition term61 := real_of_num (NUMERAL 0).
Definition term63 (x0 : nat) (x1 : nat) := Peano.le (Nat.add x0 x1) (NUMERAL 0).
Definition term35 (x0 : nat) (x1 : nat) := real_le (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term16 (x0 : nat) (x1 : nat) := real_add (real_of_num x0) (real_of_num x1).
Definition term10 (x0 : nat) := forall y0 : nat, (real_le (real_of_num x0) (real_of_num y0)) = (Peano.le x0 y0).
Definition term66 (x0 : nat) (x1 : nat) := @eq Prop ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0))).
Definition term40 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_neg (real_of_num x1)).
Definition term47 (x0 : nat) (x1 : nat) := real_le (real_of_num (NUMERAL 0)) (real_add (real_of_num x0) (real_of_num x1)).
Definition term56 (x0 : nat) (x1 : nat) := real_le (real_of_num (NUMERAL 0)) (real_of_num (Nat.add x0 x1)).
Definition term37 (x0 : nat) (x1 : nat) := @eq Prop (real_le (real_of_num x0) (real_of_num x1)).
Definition term48 (x0 : nat) (x1 : nat) := and (real_le (real_of_num (NUMERAL 0)) (real_add (real_of_num x0) (real_of_num x1))).
Definition term7 (x0 : nat) := (fun y0 : nat => Peano.le (NUMERAL 0) y0) x0.
Definition term39 (x0 : nat) (x1 : nat) := and ((real_le (real_of_num x0) (real_of_num x1)) = (Peano.le x0 x1)).
Definition term53 (x0 : nat) (x1 : nat) := ((real_le (real_of_num x0) (real_of_num x1)) = (Peano.le x0 x1)) /\ (((real_le (real_of_num x1) (real_of_num x0)) = (Peano.le x1 x0)) /\ ((real_le (real_add (real_of_num x0) (real_of_num x1)) (real_of_num (NUMERAL 0))) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0))))).
Definition term44 (x0 : nat) (x1 : nat) := ((real_le (real_of_num x0) (real_of_num x1)) = (Peano.le x0 x1)) /\ (((real_le (real_of_num x1) (real_of_num x0)) = (Peano.le x1 x0)) /\ ((real_le (real_of_num x0) (real_neg (real_of_num x1))) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0))))).
Definition term43 (x0 : nat) (x1 : nat) := ((real_le (real_of_num x0) (real_of_num x1)) = (Peano.le x0 x1)) /\ (((real_le (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (Peano.le x1 x0)) /\ ((real_le (real_of_num x0) (real_neg (real_of_num x1))) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0))))).
Definition term1 (x0 : nat) := forall y0 : nat, ((Nat.add x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0))).
Definition term55 := real_le (real_of_num (NUMERAL 0)).
Definition term15 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_add (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.add x0 y0))) x1.
Definition term21 (x0 : real) (x1 : real) := real_le x0 (real_neg x1).
Definition term3 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term31 (x0 : real) (x1 : real) := real_le (real_neg x0) (real_neg x1).
Definition term60 (x0 : nat) (x1 : nat) := real_le (real_of_num (Nat.add x0 x1)).
Definition term32 (x0 : nat) (x1 : nat) := real_le (real_neg (real_of_num x0)) (real_of_num x1).
Definition term11 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_le (real_of_num x0) (real_of_num y0)) = (Peano.le x0 y0)) x1.
Definition term52 (x0 : nat) (x1 : nat) := ((real_le (real_of_num x1) (real_of_num x0)) = (Peano.le x1 x0)) /\ ((real_le (real_add (real_of_num x0) (real_of_num x1)) (real_of_num (NUMERAL 0))) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))).
Definition term42 (x0 : nat) (x1 : nat) := ((real_le (real_of_num x1) (real_of_num x0)) = (Peano.le x1 x0)) /\ ((real_le (real_of_num x0) (real_neg (real_of_num x1))) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))).
Definition term41 (x0 : nat) (x1 : nat) := ((real_le (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (Peano.le x1 x0)) /\ ((real_le (real_of_num x0) (real_neg (real_of_num x1))) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))).
Definition term25 (x0 : real) (x1 : real) := (fun y0 : real => (real_le (real_neg x0) y0) = (real_le (real_of_num (NUMERAL 0)) (real_add x0 y0))) x1.
Definition term65 (x0 : nat) (x1 : nat) := True /\ ((Peano.le (Nat.add x0 x1) (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))).
Definition term29 (x0 : real) := forall y0 : real, (real_le (real_neg x0) (real_neg y0)) = (real_le y0 x0).
Definition term28 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le (real_neg y0) (real_neg y1)) = (real_le y1 y0)) x0.
Definition term23 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le (real_neg y0) y1) = (real_le (real_of_num (NUMERAL 0)) (real_add y0 y1))) x0.
Definition term18 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 (real_neg y1)) = (real_le (real_add y0 y1) (real_of_num (NUMERAL 0)))) x0.
Definition term19 (x0 : real) := forall y0 : real, (real_le x0 (real_neg y0)) = (real_le (real_add x0 y0) (real_of_num (NUMERAL 0))).
Definition term8 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term38 (x0 : nat) (x1 : nat) := and ((real_le (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) = (Peano.le x0 x1)).
Definition term62 (x0 : nat) (x1 : nat) := real_le (real_of_num (Nat.add x0 x1)) (real_of_num (NUMERAL 0)).
Definition term57 (x0 : nat) (x1 : nat) := Peano.le (NUMERAL 0) (Nat.add x0 x1).
Definition term33 (x0 : nat) (x1 : nat) := and ((real_le (real_neg (real_of_num x0)) (real_of_num x1)) = True).
Definition term58 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le x0 x1).
Definition term27 (x0 : real) (x1 : real) := real_le (real_of_num (NUMERAL 0)) (real_add x0 x1).
Definition term54 (x0 : nat) (x1 : nat) := (real_le (real_of_num (NUMERAL 0)) (real_add (real_of_num x0) (real_of_num x1))) /\ (((real_le (real_of_num x0) (real_of_num x1)) = (Peano.le x0 x1)) /\ (((real_le (real_of_num x1) (real_of_num x0)) = (Peano.le x1 x0)) /\ ((real_le (real_add (real_of_num x0) (real_of_num x1)) (real_of_num (NUMERAL 0))) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))))).
Definition term45 (x0 : nat) (x1 : nat) := ((real_le (real_neg (real_of_num x0)) (real_of_num x1)) = True) /\ (((real_le (real_of_num x0) (real_of_num x1)) = (Peano.le x0 x1)) /\ (((real_le (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (Peano.le x1 x0)) /\ ((real_le (real_of_num x0) (real_neg (real_of_num x1))) = ((x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)))))).
Definition term51 (x0 : nat) (x1 : nat) := @eq Prop (real_le (real_add (real_of_num x0) (real_of_num x1)) (real_of_num (NUMERAL 0))).
Definition term13 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) x0.
Definition term9 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_le (real_of_num y0) (real_of_num y1)) = (Peano.le y0 y1)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) x0.
Definition term14 (x0 : nat) := forall y0 : nat, (real_add (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.add x0 y0)).
Definition term4 := forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term49 (x0 : nat) (x1 : nat) := real_le (real_add (real_of_num x0) (real_of_num x1)) (real_of_num (NUMERAL 0)).
Definition term30 (x0 : real) (x1 : real) := (fun y0 : real => (real_le (real_neg x0) (real_neg y0)) = (real_le y0 x0)) x1.
Definition term20 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 (real_neg y0)) = (real_le (real_add x0 y0) (real_of_num (NUMERAL 0)))) x1.
Definition term22 (x0 : real) (x1 : real) := real_le (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term36 (x0 : nat) (x1 : nat) := @eq Prop (real_le (real_neg (real_of_num x0)) (real_neg (real_of_num x1))).
Definition term34 (x0 : nat) (x1 : nat) := and (real_le (real_neg (real_of_num x0)) (real_of_num x1)).
Definition term12 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_of_num x1).
Definition term59 (x0 : nat) (x1 : nat) := real_le (real_add (real_of_num x0) (real_of_num x1)).
Definition term24 (x0 : real) := forall y0 : real, (real_le (real_neg x0) y0) = (real_le (real_of_num (NUMERAL 0)) (real_add x0 y0)).
Definition term6 (x0 : nat) := Peano.le x0 (NUMERAL 0).
Definition term17 (x0 : nat) (x1 : nat) := real_of_num (Nat.add x0 x1).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.add x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) x1.
