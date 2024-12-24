Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term9 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := (~ x0) -> x1 = x2.
Definition term89 (a0 : Type') (x0 : a0) := fun y0 : a0 => ((@COND a0 True x0 y0) = x0) /\ ((@COND a0 False x0 y0) = y0).
Definition term7 (x0 : Prop) := imp (~ x0).
Definition term46 (a0 : Type') (x0 : a0) := fun y0 : a0 => x0.
Definition term91 (a0 : Type') (x0 : a0) := forall y0 : a0, ((@COND a0 True x0 y0) = x0) /\ ((@COND a0 False x0 y0) = y0).
Definition term23 (a0 : Type') (x0 : type1537 a0) (x1 : Prop) := (fun y0 : Prop => x0 y0) x1.
Definition term5 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := and (x0 -> x1 = x2).
Definition term69 (a0 : Type') (x0 : a0) (x1 : a0) := (~ False) -> x0 = x1.
Definition term87 (a0 : Type') (x0 : a0) (x1 : a0) := @eq a0 (@COND a0 False x0 x1).
Definition term36 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := (True -> x1 = x0) /\ ((~ True) -> x1 = x2).
Definition term10 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : a0) (x3 : a0) := ((x1 = True) -> x2 = x0) /\ ((x1 = False) -> x2 = x3).
Definition term93 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term1 (x0 : Prop) := imp (x0 = True).
Definition term81 (a0 : Type') (x0 : a0) := @eq (a0 -> a0) ((fun y0 : a0 => fun y1 : a0 => y1) x0).
Definition term27 (a0 : Type') := @eq (a0 -> a0 -> a0) ((fun y0 : Prop => (fun y1 : Prop => fun y2 : a0 => fun y3 : a0 => @ε a0 (fun y4 : a0 => (y1 -> y4 = y2) /\ ((~ y1) -> y4 = y3))) y0) True).
Definition term77 (a0 : Type') (x0 : a0) := (fun y0 : a0 => fun y1 : a0 => y1) x0.
Definition term92 (a0 : Type') := forall y0 : a0, True.
Definition term11 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : a0) (x3 : a0) := (x1 -> x2 = x0) /\ ((~ x1) -> x2 = x3).
Definition term56 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => (fun y1 : a0 => x0) y0) x1.
Definition term86 (a0 : Type') (x0 : a0) := @eq a0 ((fun y0 : a0 => y0) x0).
Definition term53 (a0 : Type') (x0 : a0) := @eq (a0 -> a0) ((fun y0 : a0 => fun y1 : a0 => y0) x0).
Definition term51 (a0 : Type') := fun y0 : a0 => (fun y1 : a0 => fun y2 : a0 => y1) y0.
Definition term2 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := (x0 = True) -> x1 = x2.
Definition term94 (a0 : Type') := fun y0 : a0 => forall y1 : a0, ((@COND a0 True y0 y1) = y0) /\ ((@COND a0 False y0 y1) = y1).
Definition term85 (a0 : Type') (x0 : a0) := @eq a0 ((fun y0 : a0 => (fun y1 : a0 => y1) y0) x0).
Definition term12 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : a0) := fun y0 : a0 => ((x1 = True) -> y0 = x0) /\ ((x1 = False) -> y0 = x2).
Definition term21 (a0 : Type') := (fun y0 : Prop => fun y1 : a0 => fun y2 : a0 => @ε a0 (fun y3 : a0 => (y0 -> y3 = y1) /\ ((~ y0) -> y3 = y2))) True.
Definition term71 (a0 : Type') (x0 : a0) (x1 : a0) := True /\ (x0 = x1).
Definition term24 (a0 : Type') := (fun y0 : Prop => (fun y1 : Prop => fun y2 : a0 => fun y3 : a0 => @ε a0 (fun y4 : a0 => (y1 -> y4 = y2) /\ ((~ y1) -> y4 = y3))) y0) True.
Definition term83 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (fun y1 : a0 => y1) y0) x0.
Definition term20 (a0 : Type') := fun y0 : Prop => fun y1 : a0 => fun y2 : a0 => @ε a0 (fun y3 : a0 => (y0 -> y3 = y1) /\ ((~ y0) -> y3 = y2)).
Definition term0 (a0 : Type') := fun y0 : Prop => fun y1 : a0 => fun y2 : a0 => @ε a0 (fun y3 : a0 => ((y0 = True) -> y3 = y1) /\ ((y0 = False) -> y3 = y2)).
Definition term67 (a0 : Type') (x0 : a0) (x1 : a0) := and (False -> x0 = x1).
Definition term35 (a0 : Type') (x0 : a0) (x1 : a0) := False -> x0 = x1.
Definition term72 (a0 : Type') (x0 : a0) (x1 : a0) := fun y0 : a0 => (False -> y0 = x0) /\ ((~ False) -> y0 = x1).
Definition term42 (a0 : Type') (x0 : a0) := (fun y0 : a0 => y0 = x0) (@ε a0 (fun y0 : a0 => y0 = x0)).
Definition term88 (a0 : Type') (x0 : a0) (x1 : a0) := ((@COND a0 True x0 x1) = x0) /\ ((@COND a0 False x0 x1) = x1).
Definition term37 (a0 : Type') (x0 : a0) (x1 : a0) := (x0 = x1) /\ True.
Definition term38 (a0 : Type') (x0 : a0) (x1 : a0) := fun y0 : a0 => (True -> y0 = x0) /\ ((~ True) -> y0 = x1).
Definition term26 (a0 : Type') := fun y0 : Prop => (fun y1 : Prop => fun y2 : a0 => fun y3 : a0 => @ε a0 (fun y4 : a0 => (y1 -> y4 = y2) /\ ((~ y1) -> y4 = y3))) y0.
Definition term43 (a0 : Type') (x0 : a0) := @eq Prop ((fun y0 : a0 => y0 = x0) (@ε a0 (fun y0 : a0 => y0 = x0))).
Definition term25 (a0 : Type') (x0 : Prop) := (fun y0 : Prop => fun y1 : a0 => fun y2 : a0 => @ε a0 (fun y3 : a0 => (y0 -> y3 = y1) /\ ((~ y0) -> y3 = y2))) x0.
Definition term57 (a0 : Type') (x0 : a0) := fun y0 : a0 => (fun y1 : a0 => x0) y0.
Definition term55 (a0 : Type') (x0 : a0 -> a0) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term22 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term74 (a0 : Type') (x0 : a0) := fun y0 : a0 => @ε a0 (fun y1 : a0 => (False -> y1 = x0) /\ ((~ False) -> y1 = y0)).
Definition term45 (a0 : Type') (x0 : a0) := fun y0 : a0 => @ε a0 (fun y1 : a0 => (True -> y1 = x0) /\ ((~ True) -> y1 = y0)).
Definition term17 (a0 : Type') (x0 : a0) (x1 : Prop) := fun y0 : a0 => @ε a0 (fun y1 : a0 => (x1 -> y1 = x0) /\ ((~ x1) -> y1 = y0)).
Definition term16 (a0 : Type') (x0 : a0) (x1 : Prop) := fun y0 : a0 => @ε a0 (fun y1 : a0 => ((x1 = True) -> y1 = x0) /\ ((x1 = False) -> y1 = y0)).
Definition term90 (a0 : Type') := fun y0 : a0 => True.
Definition term49 (a0 : Type') (x0 : type1400 a0) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term34 (a0 : Type') (x0 : a0) (x1 : a0) := (~ True) -> x0 = x1.
Definition term82 (a0 : Type') (x0 : a0) := (fun y0 : a0 => y0) x0.
Definition term73 (a0 : Type') (x0 : a0) (x1 : a0) := @ε a0 (fun y0 : a0 => (False -> y0 = x0) /\ ((~ False) -> y0 = x1)).
Definition term40 (a0 : Type') (x0 : a0) (x1 : a0) := @ε a0 (fun y0 : a0 => (True -> y0 = x0) /\ ((~ True) -> y0 = x1)).
Definition term6 (x0 : Prop) := imp (x0 = False).
Definition term58 (a0 : Type') (x0 : a0) (x1 : a0) := @eq a0 ((fun y0 : a0 => (fun y1 : a0 => x0) y0) x1).
Definition term75 (a0 : Type') := fun y0 : a0 => y0.
Definition term50 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (fun y1 : a0 => fun y2 : a0 => y1) y0) x0.
Definition term66 (a0 : Type') := fun y0 : a0 => fun y1 : a0 => @ε a0 (fun y2 : a0 => (False -> y2 = y0) /\ ((~ False) -> y2 = y1)).
Definition term29 (a0 : Type') := fun y0 : a0 => fun y1 : a0 => @ε a0 (fun y2 : a0 => (True -> y2 = y0) /\ ((~ True) -> y2 = y1)).
Definition term19 (a0 : Type') (x0 : Prop) := fun y0 : a0 => fun y1 : a0 => @ε a0 (fun y2 : a0 => (x0 -> y2 = y0) /\ ((~ x0) -> y2 = y1)).
Definition term18 (a0 : Type') (x0 : Prop) := fun y0 : a0 => fun y1 : a0 => @ε a0 (fun y2 : a0 => ((x0 = True) -> y2 = y0) /\ ((x0 = False) -> y2 = y1)).
Definition term60 (a0 : Type') (x0 : a0) (x1 : a0) := @eq a0 (@COND a0 True x0 x1).
Definition term32 (a0 : Type') (x0 : a0) (x1 : a0) := and (x0 = x1).
Definition term68 := imp (~ False).
Definition term39 (a0 : Type') (x0 : a0) := fun y0 : a0 => y0 = x0.
Definition term44 (a0 : Type') (x0 : a0) := @eq Prop ((@ε a0 (fun y0 : a0 => y0 = x0)) = x0).
Definition term15 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : a0) := @ε a0 (fun y0 : a0 => (x1 -> y0 = x0) /\ ((~ x1) -> y0 = x2)).
Definition term70 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := (False -> x1 = x0) /\ ((~ False) -> x1 = x2).
Definition term80 (a0 : Type') (x0 : a0) := @eq (a0 -> a0) ((fun y0 : a0 => (fun y1 : a0 => fun y2 : a0 => y2) y0) x0).
Definition term52 (a0 : Type') (x0 : a0) := @eq (a0 -> a0) ((fun y0 : a0 => (fun y1 : a0 => fun y2 : a0 => y1) y0) x0).
Definition term13 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : a0) := fun y0 : a0 => (x1 -> y0 = x0) /\ ((~ x1) -> y0 = x2).
Definition term41 (a0 : Type') (x0 : a0) := @ε a0 (fun y0 : a0 => y0 = x0).
Definition term61 (a0 : Type') (x0 : a0) (x1 : a0) := and ((@COND a0 True x1 x0) = x1).
Definition term64 (a0 : Type') := @eq (a0 -> a0 -> a0) ((fun y0 : Prop => (fun y1 : Prop => fun y2 : a0 => fun y3 : a0 => @ε a0 (fun y4 : a0 => (y1 -> y4 = y2) /\ ((~ y1) -> y4 = y3))) y0) False).
Definition term63 (a0 : Type') := (fun y0 : Prop => (fun y1 : Prop => fun y2 : a0 => fun y3 : a0 => @ε a0 (fun y4 : a0 => (y1 -> y4 = y2) /\ ((~ y1) -> y4 = y3))) y0) False.
Definition term95 (a0 : Type') := forall y0 : a0, forall y1 : a0, ((@COND a0 True y0 y1) = y0) /\ ((@COND a0 False y0 y1) = y1).
Definition term48 (a0 : Type') (x0 : a0) := (fun y0 : a0 => fun y1 : a0 => y0) x0.
Definition term47 (a0 : Type') := fun y0 : a0 => fun y1 : a0 => y0.
Definition term30 (a0 : Type') (x0 : a0) (x1 : a0) := True -> x0 = x1.
Definition term28 (a0 : Type') := @eq (a0 -> a0 -> a0) ((fun y0 : Prop => fun y1 : a0 => fun y2 : a0 => @ε a0 (fun y3 : a0 => (y0 -> y3 = y1) /\ ((~ y0) -> y3 = y2))) True).
Definition term33 := imp (~ True).
Definition term65 (a0 : Type') := @eq (a0 -> a0 -> a0) ((fun y0 : Prop => fun y1 : a0 => fun y2 : a0 => @ε a0 (fun y3 : a0 => (y0 -> y3 = y1) /\ ((~ y0) -> y3 = y2))) False).
Definition term59 (a0 : Type') (x0 : a0) (x1 : a0) := @eq a0 ((fun y0 : a0 => x0) x1).
Definition term62 (a0 : Type') := (fun y0 : Prop => fun y1 : a0 => fun y2 : a0 => @ε a0 (fun y3 : a0 => (y0 -> y3 = y1) /\ ((~ y0) -> y3 = y2))) False.
Definition term84 (a0 : Type') := fun y0 : a0 => (fun y1 : a0 => y1) y0.
Definition term31 (a0 : Type') (x0 : a0) (x1 : a0) := and (True -> x0 = x1).
Definition term8 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := (x0 = False) -> x1 = x2.
Definition term3 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := x0 -> x1 = x2.
Definition term4 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := and ((x0 = True) -> x1 = x2).
Definition term14 (a0 : Type') (x0 : a0) (x1 : Prop) (x2 : a0) := @ε a0 (fun y0 : a0 => ((x1 = True) -> y0 = x0) /\ ((x1 = False) -> y0 = x2)).
Definition term76 (a0 : Type') := fun y0 : a0 => fun y1 : a0 => y1.
Definition term78 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (fun y1 : a0 => fun y2 : a0 => y2) y0) x0.
Definition term54 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => x0) x1.
Definition term79 (a0 : Type') := fun y0 : a0 => (fun y1 : a0 => fun y2 : a0 => y2) y0.
