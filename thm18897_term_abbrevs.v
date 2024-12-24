Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term88 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (x0 x2)) \/ ((~ (x0 x1)) \/ (x1 = x2)).
Definition term84 (a0 : Type') (x0 : a0 -> Prop) := and (exists y0 : a0, x0 y0).
Definition term55 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => forall y1 : a0, ((x0 y0) /\ (x0 y1)) -> y0 = y1.
Definition term20 := or (~ True).
Definition term76 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (~ (x0 x1)).
Definition term16 (x0 : Prop) (x1 : Prop) := (~ False) \/ ((~ x0) \/ x1).
Definition term1 (a0 : Type') (x0 : a0) := forall y0 : a0, (x0 = y0) = (y0 = x0).
Definition term19 (x0 : Prop) (x1 : Prop) := @eq Prop (x0 -> x1).
Definition term37 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 => x0 y0.
Definition term80 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => (~ ((fun y1 : a0 => x0 y1) x1)) \/ ((~ ((fun y1 : a0 => x0 y1) y0)) \/ (x1 = y0)).
Definition term7 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((y0 /\ x0) -> x1) = ((~ y0) \/ ((~ x0) \/ x1))) True.
Definition term8 (x0 : Prop) (x1 : Prop) := (True /\ x0) -> x1.
Definition term9 (x0 : Prop) (x1 : Prop) := (~ True) \/ ((~ x0) \/ x1).
Definition term43 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => x0 y0.
Definition term74 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (ex y0) /\ (forall y1 : a0, forall y2 : a0, (~ (y0 y1)) \/ ((~ (y0 y2)) \/ (y1 = y2)))) x0.
Definition term91 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => forall y1 : a0, (~ (x0 y0)) \/ ((~ (x0 y1)) \/ (y1 = y0)).
Definition term82 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => forall y1 : a0, (~ ((fun y2 : a0 => x0 y2) y0)) \/ ((~ ((fun y2 : a0 => x0 y2) y1)) \/ (y0 = y1)).
Definition term56 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => forall y1 : a0, (~ (x0 y0)) \/ ((~ (x0 y1)) \/ (y0 = y1)).
Definition term65 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => x0 y0) x1.
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (x0 x1)) \/ ((~ (x0 x2)) \/ (x1 = x2)).
Definition term61 (a0 : Type') (x0 : a0 -> Prop) := (ex x0) /\ (forall y0 : a0, forall y1 : a0, (~ (x0 y0)) \/ ((~ (x0 y1)) \/ (y0 = y1))).
Definition term60 (a0 : Type') (x0 : a0 -> Prop) := (ex x0) /\ (forall y0 : a0, forall y1 : a0, ((x0 y0) /\ (x0 y1)) -> y0 = y1).
Definition term34 (x0 : Prop) := imp (False /\ x0).
Definition term85 (a0 : Type') (x0 : a0 -> Prop) := (exists y0 : a0, x0 y0) /\ (forall y0 : a0, forall y1 : a0, (~ (x0 y0)) \/ ((~ (x0 y1)) \/ (y0 = y1))).
Definition term71 (a0 : Type') (x0 : a0 -> Prop) := (exists y0 : a0, x0 y0) /\ (forall y0 : a0, forall y1 : a0, (~ ((fun y2 : a0 => x0 y2) y0)) \/ ((~ ((fun y2 : a0 => x0 y2) y1)) \/ (y0 = y1))).
Definition term47 (a0 : Type') (x0 : a0 -> Prop) := (exists y0 : a0, x0 y0) /\ (forall y0 : a0, forall y1 : a0, (~ (x0 y0)) \/ ((~ (x0 y1)) \/ (y1 = y0))).
Definition term53 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, ((x0 x1) /\ (x0 y0)) -> x1 = y0.
Definition term17 (x0 : Prop) := imp (True /\ x0).
Definition term0 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, (y0 = y1) = (y1 = y0)) x0.
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ((x0 x1) /\ (x0 x2)) -> x1 = x2.
Definition term32 (x0 : Prop) := @eq Prop (False -> x0).
Definition term30 (x0 : Prop) := (~ False) \/ x0.
Definition term33 := or (~ False).
Definition term42 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => y0 = (fun y1 : a0 => y0 y1)) x0.
Definition term79 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ ((fun y0 : a0 => x0 y0) x1)) \/ ((~ ((fun y0 : a0 => x0 y0) x2)) \/ (x1 = x2)).
Definition term23 (x0 : Prop) := fun y0 : Prop => (y0 -> x0) = ((~ y0) \/ x0).
Definition term13 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop (((x0 /\ x1) -> x2) = ((~ x0) \/ ((~ x1) \/ x2))).
Definition term66 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => (ex y1) /\ (forall y2 : a0, forall y3 : a0, (~ (y1 y2)) \/ ((~ (y1 y3)) \/ (y2 = y3)))) y0) (fun y0 : a0 => x0 y0).
Definition term78 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (x0 x2)) \/ (x1 = x2).
Definition term26 (x0 : Prop) := (~ True) \/ x0.
Definition term64 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term70 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop ((fun y0 : a0 -> Prop => (ex y0) /\ (forall y1 : a0, forall y2 : a0, (~ (y0 y1)) \/ ((~ (y0 y2)) \/ (y1 = y2)))) (fun y0 : a0 => x0 y0)).
Definition term77 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ ((fun y0 : a0 => x0 y0) x2)) \/ (x1 = x2).
Definition term72 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term69 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop ((fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => (ex y1) /\ (forall y2 : a0, forall y3 : a0, (~ (y1 y2)) \/ ((~ (y1 y3)) \/ (y2 = y3)))) y0) (fun y0 : a0 => x0 y0)).
Definition term12 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (~ x0) \/ ((~ x1) \/ x2).
Definition term90 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, (~ (x0 x1)) \/ ((~ (x0 y0)) \/ (y0 = x1)).
Definition term81 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, (~ ((fun y1 : a0 => x0 y1) x1)) \/ ((~ ((fun y1 : a0 => x0 y1) y0)) \/ (x1 = y0)).
Definition term54 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, (~ (x0 x1)) \/ ((~ (x0 y0)) \/ (x1 = y0)).
Definition term41 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, y0 = (fun y1 : a0 => y0 y1).
Definition term5 (x0 : Prop) (x1 : Prop) := fun y0 : Prop => ((y0 /\ x0) -> x1) = ((~ y0) \/ ((~ x0) \/ x1)).
Definition term22 (x0 : Prop) (x1 : Prop) := False \/ ((~ x0) \/ x1).
Definition term2 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => (x0 = y0) = (y0 = x0)) x1.
Definition term27 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => (y0 -> x0) = ((~ y0) \/ x0)) x1).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => ((y0 /\ x0) -> x1) = ((~ y0) \/ ((~ x0) \/ x1))) x2.
Definition term4 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term11 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) -> x2.
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => ((x0 x1) /\ (x0 y0)) -> x1 = y0.
Definition term36 (x0 : Prop) (x1 : Prop) := True \/ ((~ x0) \/ x1).
Definition term44 (a0 : Type') (x0 : a0 -> Prop) := @ex1 a0 (fun y0 : a0 => x0 y0).
Definition term35 (x0 : Prop) (x1 : Prop) := @eq Prop ((False /\ x0) -> x1).
Definition term18 (x0 : Prop) (x1 : Prop) := @eq Prop ((True /\ x0) -> x1).
Definition term14 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((y0 /\ x0) -> x1) = ((~ y0) \/ ((~ x0) \/ x1))) False.
Definition term46 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (@ex1 a0 (fun y0 : a0 => x0 y0)).
Definition term63 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (ex y0) /\ (forall y1 : a0, forall y2 : a0, (~ (y0 y1)) \/ ((~ (y0 y2)) \/ (y1 = y2)))) (fun y0 : a0 => x0 y0).
Definition term59 (a0 : Type') (x0 : a0 -> Prop) := and (ex x0).
Definition term38 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => (fun y1 : a0 => y0 y1) = y0.
Definition term92 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, forall y1 : a0, (~ (x0 y0)) \/ ((~ (x0 y1)) \/ (y1 = y0)).
Definition term83 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, forall y1 : a0, (~ ((fun y2 : a0 => x0 y2) y0)) \/ ((~ ((fun y2 : a0 => x0 y2) y1)) \/ (y0 = y1)).
Definition term58 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, forall y1 : a0, (~ (x0 y0)) \/ ((~ (x0 y1)) \/ (y0 = y1)).
Definition term57 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, forall y1 : a0, ((x0 y0) /\ (x0 y1)) -> y0 = y1.
Definition term68 (a0 : Type') := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => (ex y1) /\ (forall y2 : a0, forall y3 : a0, (~ (y1 y2)) \/ ((~ (y1 y3)) \/ (y2 = y3)))) y0.
Definition term62 (a0 : Type') := fun y0 : a0 -> Prop => (ex y0) /\ (forall y1 : a0, forall y2 : a0, (~ (y0 y1)) \/ ((~ (y0 y2)) \/ (y1 = y2))).
Definition term48 (a0 : Type') := fun y0 : a0 -> Prop => (ex y0) /\ (forall y1 : a0, forall y2 : a0, ((y0 y1) /\ (y0 y2)) -> y1 = y2).
Definition term39 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => y0 = (fun y1 : a0 => y0 y1).
Definition term52 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => (~ (x0 x1)) \/ ((~ (x0 y0)) \/ (x1 = y0)).
Definition term45 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (@ex1 a0 x0).
Definition term21 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term31 (x0 : Prop) := @eq Prop (True -> x0).
Definition term89 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => (~ (x0 x1)) \/ ((~ (x0 y0)) \/ (y0 = x1)).
Definition term86 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop ((exists y0 : a0, x0 y0) /\ (forall y0 : a0, forall y1 : a0, (~ (x0 y0)) \/ ((~ (x0 y1)) \/ (y0 = y1)))).
Definition term75 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (~ ((fun y0 : a0 => x0 y0) x1)).
Definition term40 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, (fun y1 : a0 => y0 y1) = y0.
Definition term24 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 -> x0) = ((~ y0) \/ x0)) x1.
Definition term3 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term15 (x0 : Prop) (x1 : Prop) := (False /\ x0) -> x1.
Definition term87 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (x0 x1)) \/ (x1 = x2).
Definition term29 (x0 : Prop) := (fun y0 : Prop => (y0 -> x0) = ((~ y0) \/ x0)) False.
Definition term25 (x0 : Prop) := (fun y0 : Prop => (y0 -> x0) = ((~ y0) \/ x0)) True.
Definition term10 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop ((fun y0 : Prop => ((y0 /\ x0) -> x1) = ((~ y0) \/ ((~ x0) \/ x1))) x2).
Definition term73 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ ((fun y0 : a0 => x0 y0) x1).
Definition term28 (x0 : Prop) (x1 : Prop) := @eq Prop ((x0 -> x1) = ((~ x0) \/ x1)).
