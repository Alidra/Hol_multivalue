Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term80 (x0 : int) := ((int_of_real (real_of_int x0)) = x0) -> (real_of_int (int_of_real (real_of_int x0))) = (real_of_int x0).
Definition term23 (x0 : int -> Prop) := exists y0 : int, ~ (x0 y0).
Definition term22 (x0 : int -> Prop) := ~ (all x0).
Definition term93 := (~ False) -> False.
Definition term44 (x0 : real) := (integer x0) \/ (~ ((real_of_int (int_of_real x0)) = x0)).
Definition term1 := forall y0 : int, integer (real_of_int y0).
Definition term66 (x0 : int) (x1 : int) := (~ (x0 = x1)) \/ ((real_of_int x0) = (real_of_int x1)).
Definition term76 (x0 : Prop) := ~ (~ x0).
Definition term14 := fun y0 : real => (integer y0) = ((real_of_int (int_of_real y0)) = y0).
Definition term57 := and (forall y0 : real, (integer y0) \/ (~ ((real_of_int (int_of_real y0)) = y0))).
Definition term43 (x0 : real) := (fun y0 : real => (integer y0) \/ (~ ((real_of_int (int_of_real y0)) = y0))) x0.
Definition term26 (x0 : int) := ~ ((fun y0 : int => integer (real_of_int y0)) x0).
Definition term82 (x0 : int) := (~ ((real_of_int (int_of_real (real_of_int x0))) = (real_of_int x0))) -> (real_of_int (int_of_real (real_of_int x0))) = (real_of_int x0).
Definition term64 (x0 : int) (x1 : int) := (x0 = x1) -> (real_of_int x0) = (real_of_int x1).
Definition term48 (x0 : real) := (~ (integer x0)) \/ ((real_of_int (int_of_real x0)) = x0).
Definition term56 := and (forall y0 : real, (fun y1 : real => (integer y1) \/ (~ ((real_of_int (int_of_real y1)) = y1))) y0).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term29 := fun y0 : int => ~ (integer (real_of_int y0)).
Definition term84 (x0 : real) := (~ (~ ((real_of_int (int_of_real x0)) = x0))) -> integer x0.
Definition term25 (x0 : int) := (fun y0 : int => integer (real_of_int y0)) x0.
Definition term4 := (~ (forall y0 : int, integer (real_of_int y0))) -> ((forall y0 : int, (int_of_real (real_of_int y0)) = y0) /\ (forall y0 : real, (integer y0) = ((real_of_int (int_of_real y0)) = y0))) -> False.
Definition term74 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term40 := (forall y0 : real, (fun y1 : real => (integer y1) \/ (~ ((real_of_int (int_of_real y1)) = y1))) y0) /\ (forall y0 : real, (fun y1 : real => (~ (integer y1)) \/ ((real_of_int (int_of_real y1)) = y1)) y0).
Definition term88 (x0 : real) := imp ((real_of_int (int_of_real x0)) = x0).
Definition term90 (x0 : int) := ((real_of_int (int_of_real (real_of_int x0))) = (real_of_int x0)) -> integer (real_of_int x0).
Definition term69 (x0 : Prop) := (~ x0) -> x0.
Definition term91 (x0 : int) := (~ (integer (real_of_int x0))) -> integer (real_of_int x0).
Definition term13 (x0 : real) := real_of_int (int_of_real x0).
Definition term19 := and (forall y0 : int, (int_of_real (real_of_int y0)) = y0).
Definition term33 := forall y0 : real, ((integer y0) \/ (~ ((real_of_int (int_of_real y0)) = y0))) /\ ((~ (integer y0)) \/ ((real_of_int (int_of_real y0)) = y0)).
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term17 := fun y0 : int => (int_of_real (real_of_int y0)) = y0.
Definition term16 (x0 : int) := int_of_real (real_of_int x0).
Definition term73 (x0 : int) (x1 : int) := @eq Prop (((real_of_int x0) = (real_of_int x1)) \/ (~ (x0 = x1))).
Definition term46 (x0 : real) := and ((integer x0) \/ (~ ((real_of_int (int_of_real x0)) = x0))).
Definition term27 (x0 : int) := ~ (integer (real_of_int x0)).
Definition term89 (x0 : real) := ((real_of_int (int_of_real x0)) = x0) -> integer x0.
Definition term20 (x0 : int) := integer (real_of_int x0).
Definition term52 := @eq Prop (forall y0 : real, ((integer y0) \/ (~ ((real_of_int (int_of_real y0)) = y0))) /\ ((~ (integer y0)) \/ ((real_of_int (int_of_real y0)) = y0))).
Definition term51 := @eq Prop (forall y0 : real, ((fun y1 : real => (integer y1) \/ (~ ((real_of_int (int_of_real y1)) = y1))) y0) /\ ((fun y1 : real => (~ (integer y1)) \/ ((real_of_int (int_of_real y1)) = y1)) y0)).
Definition term18 := forall y0 : int, (int_of_real (real_of_int y0)) = y0.
Definition term47 (x0 : real) := (fun y0 : real => (~ (integer y0)) \/ ((real_of_int (int_of_real y0)) = y0)) x0.
Definition term41 := fun y0 : real => (integer y0) \/ (~ ((real_of_int (int_of_real y0)) = y0)).
Definition term60 := forall y0 : real, (~ (integer y0)) \/ ((real_of_int (int_of_real y0)) = y0).
Definition term83 (x0 : int) := ~ ((real_of_int (int_of_real (real_of_int x0))) = (real_of_int x0)).
Definition term45 (x0 : real) := and ((fun y0 : real => (integer y0) \/ (~ ((real_of_int (int_of_real y0)) = y0))) x0).
Definition term68 (x0 : int) := ~ ((int_of_real (real_of_int x0)) = x0).
Definition term81 (x0 : int) := real_of_int (int_of_real (real_of_int x0)).
Definition term61 := (forall y0 : real, (integer y0) \/ (~ ((real_of_int (int_of_real y0)) = y0))) /\ (forall y0 : real, (~ (integer y0)) \/ ((real_of_int (int_of_real y0)) = y0)).
Definition term75 (x0 : int) (x1 : int) := (~ (~ (x0 = x1))) -> (real_of_int x0) = (real_of_int x1).
Definition term49 (x0 : real) := ((fun y0 : real => (integer y0) \/ (~ ((real_of_int (int_of_real y0)) = y0))) x0) /\ ((fun y0 : real => (~ (integer y0)) \/ ((real_of_int (int_of_real y0)) = y0)) x0).
Definition term92 (x0 : int) := (integer (real_of_int x0)) -> False.
Definition term53 := fun y0 : real => (fun y1 : real => (integer y1) \/ (~ ((real_of_int (int_of_real y1)) = y1))) y0.
Definition term63 (x0 : int) := (fun y0 : int => (int_of_real (real_of_int y0)) = y0) x0.
Definition term70 (x0 : int) (x1 : int) := ((real_of_int x0) = (real_of_int x1)) \/ (~ (x0 = x1)).
Definition term37 (x0 : real -> Prop) (x1 : real -> Prop) := forall y0 : real, (x0 y0) /\ (x1 y0).
Definition term15 := forall y0 : real, (integer y0) = ((real_of_int (int_of_real y0)) = y0).
Definition term21 := fun y0 : int => integer (real_of_int y0).
Definition term2 := (~ (forall y0 : int, integer (real_of_int y0))) -> False.
Definition term59 := forall y0 : real, (fun y1 : real => (~ (integer y1)) \/ ((real_of_int (int_of_real y1)) = y1)) y0.
Definition term54 := forall y0 : real, (fun y1 : real => (integer y1) \/ (~ ((real_of_int (int_of_real y1)) = y1))) y0.
Definition term3 := ~ (forall y0 : int, integer (real_of_int y0)).
Definition term86 (x0 : real) := ~ (~ ((real_of_int (int_of_real x0)) = x0)).
Definition term79 (x0 : int) (x1 : int) := imp (x0 = x1).
Definition term30 := exists y0 : int, ~ (integer (real_of_int y0)).
Definition term72 (x0 : int) (x1 : int) := @eq Prop ((~ (x0 = x1)) \/ ((real_of_int x0) = (real_of_int x1))).
Definition term9 := ~ ((forall y0 : int, (int_of_real (real_of_int y0)) = y0) /\ (forall y0 : real, (integer y0) = ((real_of_int (int_of_real y0)) = y0))).
Definition term62 := (forall y0 : int, (int_of_real (real_of_int y0)) = y0) /\ ((forall y0 : real, (integer y0) \/ (~ ((real_of_int (int_of_real y0)) = y0))) /\ (forall y0 : real, (~ (integer y0)) \/ ((real_of_int (int_of_real y0)) = y0))).
Definition term71 (x0 : int) (x1 : int) := ~ (x0 = x1).
Definition term31 (x0 : real) := ((integer x0) \/ (~ ((real_of_int (int_of_real x0)) = x0))) /\ ((~ (integer x0)) \/ ((real_of_int (int_of_real x0)) = x0)).
Definition term85 (x0 : real) := ~ ((real_of_int (int_of_real x0)) = x0).
Definition term65 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term50 := fun y0 : real => ((fun y1 : real => (integer y1) \/ (~ ((real_of_int (int_of_real y1)) = y1))) y0) /\ ((fun y1 : real => (~ (integer y1)) \/ ((real_of_int (int_of_real y1)) = y1)) y0).
Definition term58 := fun y0 : real => (fun y1 : real => (~ (integer y1)) \/ ((real_of_int (int_of_real y1)) = y1)) y0.
Definition term38 (x0 : real -> Prop) (x1 : real -> Prop) := (forall y0 : real, x0 y0) /\ (forall y0 : real, x1 y0).
Definition term8 := ((forall y0 : int, (int_of_real (real_of_int y0)) = y0) /\ (forall y0 : real, (integer y0) = ((real_of_int (int_of_real y0)) = y0))) -> False.
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term67 (x0 : int) := (~ ((int_of_real (real_of_int x0)) = x0)) -> (int_of_real (real_of_int x0)) = x0.
Definition term6 := (((~ (forall y0 : int, integer (real_of_int y0))) -> ((forall y0 : int, (int_of_real (real_of_int y0)) = y0) /\ (forall y0 : real, (integer y0) = ((real_of_int (int_of_real y0)) = y0))) -> False) -> (~ (forall y0 : int, integer (real_of_int y0))) -> ((forall y0 : int, (int_of_real (real_of_int y0)) = y0) /\ (forall y0 : real, (integer y0) = ((real_of_int (int_of_real y0)) = y0))) -> False) -> (~ (forall y0 : int, integer (real_of_int y0))) -> ((forall y0 : int, (int_of_real (real_of_int y0)) = y0) /\ (forall y0 : real, (integer y0) = ((real_of_int (int_of_real y0)) = y0))) -> False.
Definition term24 := exists y0 : int, ~ ((fun y1 : int => integer (real_of_int y1)) y0).
Definition term77 (x0 : int) (x1 : int) := ~ (~ (x0 = x1)).
Definition term7 := (((~ (forall y0 : int, integer (real_of_int y0))) -> ((forall y0 : int, (int_of_real (real_of_int y0)) = y0) /\ (forall y0 : real, (integer y0) = ((real_of_int (int_of_real y0)) = y0))) -> False) -> (~ (forall y0 : int, integer (real_of_int y0))) -> ((forall y0 : int, (int_of_real (real_of_int y0)) = y0) /\ (forall y0 : real, (integer y0) = ((real_of_int (int_of_real y0)) = y0))) -> False) -> ((~ (forall y0 : int, integer (real_of_int y0))) -> ((forall y0 : int, (int_of_real (real_of_int y0)) = y0) /\ (forall y0 : real, (integer y0) = ((real_of_int (int_of_real y0)) = y0))) -> False) -> (~ (forall y0 : int, integer (real_of_int y0))) -> ((forall y0 : int, (int_of_real (real_of_int y0)) = y0) /\ (forall y0 : real, (integer y0) = ((real_of_int (int_of_real y0)) = y0))) -> False.
Definition term28 := fun y0 : int => ~ ((fun y1 : int => integer (real_of_int y1)) y0).
Definition term34 := (forall y0 : int, (int_of_real (real_of_int y0)) = y0) /\ (forall y0 : real, ((integer y0) \/ (~ ((real_of_int (int_of_real y0)) = y0))) /\ ((~ (integer y0)) \/ ((real_of_int (int_of_real y0)) = y0))).
Definition term10 := (forall y0 : int, (int_of_real (real_of_int y0)) = y0) /\ (forall y0 : real, (integer y0) = ((real_of_int (int_of_real y0)) = y0)).
Definition term39 := forall y0 : real, ((fun y1 : real => (integer y1) \/ (~ ((real_of_int (int_of_real y1)) = y1))) y0) /\ ((fun y1 : real => (~ (integer y1)) \/ ((real_of_int (int_of_real y1)) = y1)) y0).
Definition term32 := fun y0 : real => ((integer y0) \/ (~ ((real_of_int (int_of_real y0)) = y0))) /\ ((~ (integer y0)) \/ ((real_of_int (int_of_real y0)) = y0)).
Definition term42 := fun y0 : real => (~ (integer y0)) \/ ((real_of_int (int_of_real y0)) = y0).
Definition term11 := imp (~ (forall y0 : int, integer (real_of_int y0))).
Definition term87 (x0 : real) := imp (~ (~ ((real_of_int (int_of_real x0)) = x0))).
Definition term55 := forall y0 : real, (integer y0) \/ (~ ((real_of_int (int_of_real y0)) = y0)).
Definition term5 := ((~ (forall y0 : int, integer (real_of_int y0))) -> ((forall y0 : int, (int_of_real (real_of_int y0)) = y0) /\ (forall y0 : real, (integer y0) = ((real_of_int (int_of_real y0)) = y0))) -> False) -> (~ (forall y0 : int, integer (real_of_int y0))) -> ((forall y0 : int, (int_of_real (real_of_int y0)) = y0) /\ (forall y0 : real, (integer y0) = ((real_of_int (int_of_real y0)) = y0))) -> False.
Definition term12 := (~ (forall y0 : int, integer (real_of_int y0))) -> ~ ((forall y0 : int, (int_of_real (real_of_int y0)) = y0) /\ (forall y0 : real, (integer y0) = ((real_of_int (int_of_real y0)) = y0))).
Definition term78 (x0 : int) (x1 : int) := imp (~ (~ (x0 = x1))).
