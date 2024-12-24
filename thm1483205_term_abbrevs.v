Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term44 (x0 : real -> Prop) (x1 : real) (x2 : real) := @eq Prop ((fun y0 : real => (x0 y0) = (((real_le x2 x1) /\ (x0 x1)) \/ ((real_lt x1 x2) /\ (x0 x2)))) (@COND real (real_le x2 x1) x1 x2)).
Definition term54 (x0 : real) (x1 : real -> Prop) (x2 : real) := fun y0 : Prop => (x1 x2) = ((y0 /\ (x1 x0)) \/ ((real_lt x0 x2) /\ (x1 x2))).
Definition term29 (x0 : real) (x1 : Prop) (x2 : real) (x3 : real -> Prop) (x4 : real) (x5 : real) := (x1 -> (fun y0 : real => (x3 y0) = (((real_le x4 x2) /\ (x3 x2)) \/ ((real_lt x2 x4) /\ (x3 x4)))) x0) /\ ((~ x1) -> (fun y0 : real => (x3 y0) = (((real_le x4 x2) /\ (x3 x2)) \/ ((real_lt x2 x4) /\ (x3 x4)))) x5).
Definition term39 (x0 : real -> Prop) (x1 : real) (x2 : real) := (real_le x1 x2) -> (fun y0 : real => (x0 y0) = (((real_le x1 x2) /\ (x0 x2)) \/ ((real_lt x2 x1) /\ (x0 x1)))) x2.
Definition term55 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : Prop => (x0 x1) = ((y0 /\ (x0 x2)) \/ ((real_lt x2 x1) /\ (x0 x1)))) (real_le x1 x2).
Definition term47 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : Prop => (x0 x2) = ((y0 /\ (x0 x2)) \/ ((real_lt x2 x1) /\ (x0 x1)))) (real_le x1 x2).
Definition term62 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt y0 x0) = (~ (real_le x0 y0))) x1.
Definition term5 (x0 : real) (x1 : real) := (fun y0 : real => (real_gt y0 x0) = (real_lt x0 y0)) x1.
Definition term2 (x0 : real) (x1 : real) := (fun y0 : real => (real_ge y0 x0) = (real_le x0 y0)) x1.
Definition term67 (x0 : real -> Prop) (x1 : real) := (x0 x1) \/ False.
Definition term16 (x0 : real) (x1 : real -> Prop) (x2 : real) := (real_ge x2 x0) /\ (x1 x2).
Definition term31 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (x0 y0) = (((real_le x2 x1) /\ (x0 x1)) \/ ((real_lt x1 x2) /\ (x0 x2)))) (@COND real (real_le x2 x1) x1 x2).
Definition term46 (x0 : real) (x1 : real -> Prop) (x2 : real) := fun y0 : Prop => (x1 x0) = ((y0 /\ (x1 x0)) \/ ((real_lt x0 x2) /\ (x1 x2))).
Definition term36 (x0 : real) (x1 : real -> Prop) (x2 : real) := (~ (real_le x2 x0)) -> (x1 x2) = (((real_le x2 x0) /\ (x1 x0)) \/ ((real_lt x0 x2) /\ (x1 x2))).
Definition term34 (x0 : real) (x1 : real) := imp (~ (real_le x0 x1)).
Definition term17 (x0 : real) (x1 : real -> Prop) (x2 : real) := (real_le x0 x2) /\ (x1 x2).
Definition term51 (x0 : real) (x1 : real -> Prop) (x2 : real) := @eq Prop ((x1 x0) = (((real_le x2 x0) /\ (x1 x0)) \/ ((real_lt x0 x2) /\ (x1 x2)))).
Definition term4 (x0 : real) := forall y0 : real, (real_gt y0 x0) = (real_lt x0 y0).
Definition term1 (x0 : real) := forall y0 : real, (real_ge y0 x0) = (real_le x0 y0).
Definition term19 (x0 : real) (x1 : real -> Prop) (x2 : real) := or ((real_le x0 x2) /\ (x1 x2)).
Definition term30 (x0 : real) (x1 : real -> Prop) (x2 : real) := fun y0 : real => (x1 y0) = (((real_le x2 x0) /\ (x1 x0)) \/ ((real_lt x0 x2) /\ (x1 x2))).
Definition term70 (x0 : real -> Prop) (x1 : real) := False \/ (x0 x1).
Definition term43 (x0 : real) (x1 : real -> Prop) (x2 : real) := ((real_le x2 x0) -> (x1 x0) = (((real_le x2 x0) /\ (x1 x0)) \/ ((real_lt x0 x2) /\ (x1 x2)))) /\ ((~ (real_le x2 x0)) -> (x1 x2) = (((real_le x2 x0) /\ (x1 x0)) \/ ((real_lt x0 x2) /\ (x1 x2)))).
Definition term27 (x0 : real) (x1 : Prop) (x2 : real -> Prop) (x3 : real) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term21 (x0 : real) (x1 : real) := and (real_lt x0 x1).
Definition term37 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (x0 y0) = (((real_le x1 x2) /\ (x0 x2)) \/ ((real_lt x2 x1) /\ (x0 x1)))) x2.
Definition term28 (x0 : real) (x1 : real -> Prop) (x2 : real) (x3 : Prop) (x4 : real) (x5 : real) := (fun y0 : real => (x1 y0) = (((real_le x2 x0) /\ (x1 x0)) \/ ((real_lt x0 x2) /\ (x1 x2)))) (@COND real x3 x4 x5).
Definition term22 (x0 : real) (x1 : real -> Prop) (x2 : real) := (real_gt x2 x0) /\ (x1 x2).
Definition term13 (x0 : real -> Prop) (x1 : real) (x2 : real) := @eq Prop (x0 (@COND real (real_le x2 x1) x1 x2)).
Definition term23 (x0 : real) (x1 : real -> Prop) (x2 : real) := (real_lt x0 x2) /\ (x1 x2).
Definition term42 (x0 : real) (x1 : real -> Prop) (x2 : real) := and ((real_le x2 x0) -> (x1 x0) = (((real_le x2 x0) /\ (x1 x0)) \/ ((real_lt x0 x2) /\ (x1 x2)))).
Definition term12 (x0 : real -> Prop) (x1 : real) (x2 : real) := @eq Prop (x0 (real_max x1 x2)).
Definition term14 (x0 : real) (x1 : real) := and (real_ge x0 x1).
Definition term53 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) -> (real_le x0 x1) = False.
Definition term9 (x0 : real) (x1 : real) := @COND real (real_le x1 x0) x0 x1.
Definition term24 (x0 : real) (x1 : real -> Prop) (x2 : real) := ((real_ge x0 x2) /\ (x1 x0)) \/ ((real_gt x2 x0) /\ (x1 x2)).
Definition term25 (x0 : real) (x1 : real -> Prop) (x2 : real) := ((real_le x2 x0) /\ (x1 x0)) \/ ((real_lt x0 x2) /\ (x1 x2)).
Definition term59 (x0 : real) (x1 : real -> Prop) (x2 : real) := @eq Prop ((x1 x2) = (((real_le x2 x0) /\ (x1 x0)) \/ ((real_lt x0 x2) /\ (x1 x2)))).
Definition term57 (x0 : real) (x1 : real -> Prop) (x2 : real) := (False /\ (x1 x0)) \/ ((real_lt x0 x2) /\ (x1 x2)).
Definition term60 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt y1 y0) = (~ (real_le y0 y1))) x0.
Definition term6 (x0 : real) := (fun y0 : real => forall y1 : real, (real_max y1 y0) = (@COND real (real_le y1 y0) y0 y1)) x0.
Definition term3 (x0 : real) := (fun y0 : real => forall y1 : real, (real_gt y1 y0) = (real_lt y0 y1)) x0.
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real, (real_ge y1 y0) = (real_le y0 y1)) x0.
Definition term41 (x0 : real -> Prop) (x1 : real) (x2 : real) := and ((real_le x1 x2) -> (fun y0 : real => (x0 y0) = (((real_le x1 x2) /\ (x0 x2)) \/ ((real_lt x2 x1) /\ (x0 x1)))) x2).
Definition term45 (x0 : real) (x1 : real -> Prop) (x2 : real) := @eq Prop ((x1 (@COND real (real_le x2 x0) x0 x2)) = (((real_le x2 x0) /\ (x1 x0)) \/ ((real_lt x0 x2) /\ (x1 x2)))).
Definition term64 (x0 : real -> Prop) (x1 : real) := or (True /\ (x0 x1)).
Definition term68 (x0 : real -> Prop) (x1 : real) := @eq Prop (x0 x1).
Definition term61 (x0 : real) := forall y0 : real, (real_lt y0 x0) = (~ (real_le x0 y0)).
Definition term49 (x0 : real) (x1 : real -> Prop) (x2 : real) := (True /\ (x1 x0)) \/ ((real_lt x0 x2) /\ (x1 x2)).
Definition term65 (x0 : real -> Prop) (x1 : real) := or (x0 x1).
Definition term33 (x0 : real) (x1 : real -> Prop) (x2 : real) := (fun y0 : real => (x1 y0) = (((real_le x2 x0) /\ (x1 x0)) \/ ((real_lt x0 x2) /\ (x1 x2)))) x2.
Definition term7 (x0 : real) := forall y0 : real, (real_max y0 x0) = (@COND real (real_le y0 x0) x0 y0).
Definition term32 (x0 : real) (x1 : real -> Prop) (x2 : real) := ((real_le x2 x0) -> (fun y0 : real => (x1 y0) = (((real_le x2 x0) /\ (x1 x0)) \/ ((real_lt x0 x2) /\ (x1 x2)))) x0) /\ ((~ (real_le x2 x0)) -> (fun y0 : real => (x1 y0) = (((real_le x2 x0) /\ (x1 x0)) \/ ((real_lt x0 x2) /\ (x1 x2)))) x2).
Definition term20 (x0 : real) (x1 : real) := and (real_gt x0 x1).
Definition term38 (x0 : real) (x1 : real) := imp (real_le x0 x1).
Definition term52 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term48 (x0 : real) (x1 : real -> Prop) (x2 : real) := (fun y0 : Prop => (x1 x0) = ((y0 /\ (x1 x0)) \/ ((real_lt x0 x2) /\ (x1 x2)))) True.
Definition term26 (x0 : real -> Prop) (x1 : Prop) (x2 : real) (x3 : real) := x0 (@COND real x1 x2 x3).
Definition term40 (x0 : real) (x1 : real -> Prop) (x2 : real) := (real_le x2 x0) -> (x1 x0) = (((real_le x2 x0) /\ (x1 x0)) \/ ((real_lt x0 x2) /\ (x1 x2))).
Definition term56 (x0 : real) (x1 : real -> Prop) (x2 : real) := (fun y0 : Prop => (x1 x2) = ((y0 /\ (x1 x0)) \/ ((real_lt x0 x2) /\ (x1 x2)))) False.
Definition term15 (x0 : real) (x1 : real) := and (real_le x0 x1).
Definition term66 (x0 : real -> Prop) (x1 : real) := False /\ (x0 x1).
Definition term35 (x0 : real) (x1 : real -> Prop) (x2 : real) := (~ (real_le x2 x0)) -> (fun y0 : real => (x1 y0) = (((real_le x2 x0) /\ (x1 x0)) \/ ((real_lt x0 x2) /\ (x1 x2)))) x2.
Definition term58 (x0 : real -> Prop) (x1 : real) (x2 : real) := @eq Prop ((fun y0 : Prop => (x0 x1) = ((y0 /\ (x0 x2)) \/ ((real_lt x2 x1) /\ (x0 x1)))) (real_le x1 x2)).
Definition term50 (x0 : real -> Prop) (x1 : real) (x2 : real) := @eq Prop ((fun y0 : Prop => (x0 x2) = ((y0 /\ (x0 x2)) \/ ((real_lt x2 x1) /\ (x0 x1)))) (real_le x1 x2)).
Definition term69 (x0 : real -> Prop) (x1 : real) := or (False /\ (x0 x1)).
Definition term18 (x0 : real) (x1 : real -> Prop) (x2 : real) := or ((real_ge x2 x0) /\ (x1 x2)).
Definition term11 (x0 : real -> Prop) (x1 : real) (x2 : real) := x0 (@COND real (real_le x2 x1) x1 x2).
Definition term63 (x0 : real -> Prop) (x1 : real) := True /\ (x0 x1).
Definition term10 (x0 : real -> Prop) (x1 : real) (x2 : real) := x0 (real_max x1 x2).
Definition term8 (x0 : real) (x1 : real) := (fun y0 : real => (real_max y0 x0) = (@COND real (real_le y0 x0) x0 y0)) x1.
