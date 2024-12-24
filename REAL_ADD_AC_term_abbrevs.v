Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term6 (x0 : real) (x1 : real) (x2 : real) := (((~ (((real_add x1 x0) = (real_add x0 x1)) /\ (((real_add (real_add x1 x0) x2) = (real_add x1 (real_add x0 x2))) /\ ((real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2)))))) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) -> False) -> (~ (((real_add x1 x0) = (real_add x0 x1)) /\ (((real_add (real_add x1 x0) x2) = (real_add x1 (real_add x0 x2))) /\ ((real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2)))))) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) -> False) -> (~ (((real_add x1 x0) = (real_add x0 x1)) /\ (((real_add (real_add x1 x0) x2) = (real_add x1 (real_add x0 x2))) /\ ((real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2)))))) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) -> False.
Definition term19 (x0 : real) (x1 : real) := forall y0 : real, (~ (((real_add x0 y0) = (real_add y0 x0)) /\ (((real_add (real_add x0 y0) x1) = (real_add x0 (real_add y0 x1))) /\ ((real_add x0 (real_add y0 x1)) = (real_add y0 (real_add x0 x1)))))) -> (forall y1 : real, forall y2 : real, (real_add y1 y2) = (real_add y2 y1)) -> ~ (forall y1 : real, forall y2 : real, forall y3 : real, (real_add y1 (real_add y2 y3)) = (real_add (real_add y1 y2) y3)).
Definition term56 := (~ False) -> False.
Definition term11 := imp (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)).
Definition term78 (x0 : Prop) := ~ (~ x0).
Definition term18 (x0 : real) (x1 : real) := forall y0 : real, (~ (((real_add x0 y0) = (real_add y0 x0)) /\ (((real_add (real_add x0 y0) x1) = (real_add x0 (real_add y0 x1))) /\ ((real_add x0 (real_add y0 x1)) = (real_add y0 (real_add x0 x1)))))) -> (forall y1 : real, forall y2 : real, (real_add y1 y2) = (real_add y2 y1)) -> (forall y1 : real, forall y2 : real, forall y3 : real, (real_add y1 (real_add y2 y3)) = (real_add (real_add y1 y2) y3)) -> False.
Definition term121 (x0 : real) (x1 : real) (x2 : real) := (((real_add (real_add x0 x2) x1) = (real_add x1 (real_add x0 x2))) /\ ((real_add (real_add x0 x2) x1) = (real_add x0 (real_add x1 x2)))) -> (real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2)).
Definition term107 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (~ (x0 = x1))) /\ (~ (~ (x2 = x3))).
Definition term77 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term103 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop (((real_add x0 x2) = (real_add x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term115 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_add x0 (real_add x2 x1)) = (real_add x0 (real_add x1 x2))).
Definition term61 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_add x0 (real_add x1 x2)) = (real_add x0 (real_add x1 x2))).
Definition term47 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2))).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term109 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp (~ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term83 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term2 (x0 : real) (x1 : real) (x2 : real) := (~ (((real_add x1 x0) = (real_add x0 x1)) /\ (((real_add (real_add x1 x0) x2) = (real_add x1 (real_add x0 x2))) /\ ((real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2)))))) -> False.
Definition term123 (x0 : real) (x1 : real) (x2 : real) := ((real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2))) -> False.
Definition term116 (x0 : real) (x1 : real) (x2 : real) := ((real_add x0 (real_add x2 x1)) = (real_add (real_add x0 x2) x1)) /\ ((real_add x0 (real_add x2 x1)) = (real_add x0 (real_add x1 x2))).
Definition term36 (x0 : real) := forall y0 : real, (real_add x0 y0) = (real_add y0 x0).
Definition term49 (x0 : real) (x1 : real) := (fun y0 : real => (real_add x0 y0) = (real_add y0 x0)) x1.
Definition term71 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term96 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_add (real_add x1 x2) x0) = (real_add x0 (real_add x1 x2))).
Definition term35 (x0 : real) := fun y0 : real => (real_add x0 y0) = (real_add y0 x0).
Definition term97 (x0 : real) := (~ (x0 = x0)) -> x0 = x0.
Definition term54 (x0 : Prop) := (~ x0) -> x0.
Definition term110 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp ((x0 = x1) /\ (x2 = x3)).
Definition term73 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term40 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_add (real_add x1 x0) x2) = (real_add x1 (real_add x0 x2)))) \/ (~ ((real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2)))).
Definition term75 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term93 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x0 = x2) -> (~ (x1 = x3)) \/ ((real_add x0 x1) = (real_add x2 x3)).
Definition term69 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term38 := forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0).
Definition term33 (x0 : real) := forall y0 : real, forall y1 : real, (real_add x0 (real_add y0 y1)) = (real_add (real_add x0 y0) y1).
Definition term27 := forall y0 : real, forall y1 : real, forall y2 : real, (~ (((real_add y1 y2) = (real_add y2 y1)) /\ (((real_add (real_add y1 y2) y0) = (real_add y1 (real_add y2 y0))) /\ ((real_add y1 (real_add y2 y0)) = (real_add y2 (real_add y1 y0)))))) -> (forall y3 : real, forall y4 : real, (real_add y3 y4) = (real_add y4 y3)) -> ~ (forall y3 : real, forall y4 : real, forall y5 : real, (real_add y3 (real_add y4 y5)) = (real_add (real_add y3 y4) y5)).
Definition term26 := forall y0 : real, forall y1 : real, forall y2 : real, (~ (((real_add y1 y2) = (real_add y2 y1)) /\ (((real_add (real_add y1 y2) y0) = (real_add y1 (real_add y2 y0))) /\ ((real_add y1 (real_add y2 y0)) = (real_add y2 (real_add y1 y0)))))) -> (forall y3 : real, forall y4 : real, (real_add y3 y4) = (real_add y4 y3)) -> (forall y3 : real, forall y4 : real, forall y5 : real, (real_add y3 (real_add y4 y5)) = (real_add (real_add y3 y4) y5)) -> False.
Definition term23 (x0 : real) := forall y0 : real, forall y1 : real, (~ (((real_add y0 y1) = (real_add y1 y0)) /\ (((real_add (real_add y0 y1) x0) = (real_add y0 (real_add y1 x0))) /\ ((real_add y0 (real_add y1 x0)) = (real_add y1 (real_add y0 x0)))))) -> (forall y2 : real, forall y3 : real, (real_add y2 y3) = (real_add y3 y2)) -> ~ (forall y2 : real, forall y3 : real, forall y4 : real, (real_add y2 (real_add y3 y4)) = (real_add (real_add y2 y3) y4)).
Definition term22 (x0 : real) := forall y0 : real, forall y1 : real, (~ (((real_add y0 y1) = (real_add y1 y0)) /\ (((real_add (real_add y0 y1) x0) = (real_add y0 (real_add y1 x0))) /\ ((real_add y0 (real_add y1 x0)) = (real_add y1 (real_add y0 x0)))))) -> (forall y2 : real, forall y3 : real, (real_add y2 y3) = (real_add y3 y2)) -> (forall y2 : real, forall y3 : real, forall y4 : real, (real_add y2 (real_add y3 y4)) = (real_add (real_add y2 y3) y4)) -> False.
Definition term10 := forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2).
Definition term70 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term118 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_add (real_add x0 x2) x1) = (real_add x0 (real_add x1 x2)))) -> (real_add (real_add x0 x2) x1) = (real_add x0 (real_add x1 x2)).
Definition term12 := (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) -> False.
Definition term119 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_add (real_add x0 x2) x1) = (real_add x0 (real_add x1 x2))).
Definition term104 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ ((~ (x0 = x2)) \/ (~ (x1 = x3)))) -> (real_add x0 x1) = (real_add x2 x3).
Definition term67 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term46 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_add (real_add x0 x1) x2) = (real_add x0 (real_add x1 x2))).
Definition term43 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_add x1 x0) = (real_add x0 x1))) \/ ((~ ((real_add (real_add x1 x0) x2) = (real_add x1 (real_add x0 x2)))) \/ (~ ((real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2))))).
Definition term59 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_add x0 (real_add x1 x2)) = (real_add (real_add x0 x1) x2)).
Definition term101 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_add x0 x2) = (real_add x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term126 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (~ (((real_add x0 y0) = (real_add y0 x0)) /\ (((real_add (real_add x0 y0) x1) = (real_add x0 (real_add y0 x1))) /\ ((real_add x0 (real_add y0 x1)) = (real_add y0 (real_add x0 x1)))))) -> (forall y1 : real, forall y2 : real, (real_add y1 y2) = (real_add y2 y1)) -> (forall y1 : real, forall y2 : real, forall y3 : real, (real_add y1 (real_add y2 y3)) = (real_add (real_add y1 y2) y3)) -> False) x2.
Definition term4 (x0 : real) (x1 : real) (x2 : real) := (~ (((real_add x1 x0) = (real_add x0 x1)) /\ (((real_add (real_add x1 x0) x2) = (real_add x1 (real_add x0 x2))) /\ ((real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2)))))) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) -> False.
Definition term57 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term88 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_add (real_add x0 x1) x2) = (real_add x0 (real_add x1 x2)))) -> (real_add (real_add x0 x1) x2) = (real_add x0 (real_add x1 x2)).
Definition term58 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_add x0 (real_add x1 x2)) = (real_add (real_add x0 x1) x2))) -> (real_add x0 (real_add x1 x2)) = (real_add (real_add x0 x1) x2).
Definition term21 (x0 : real) := fun y0 : real => forall y1 : real, (~ (((real_add y0 y1) = (real_add y1 y0)) /\ (((real_add (real_add y0 y1) x0) = (real_add y0 (real_add y1 x0))) /\ ((real_add y0 (real_add y1 x0)) = (real_add y1 (real_add y0 x0)))))) -> (forall y2 : real, forall y3 : real, (real_add y2 y3) = (real_add y3 y2)) -> ~ (forall y2 : real, forall y3 : real, forall y4 : real, (real_add y2 (real_add y3 y4)) = (real_add (real_add y2 y3) y4)).
Definition term20 (x0 : real) := fun y0 : real => forall y1 : real, (~ (((real_add y0 y1) = (real_add y1 y0)) /\ (((real_add (real_add y0 y1) x0) = (real_add y0 (real_add y1 x0))) /\ ((real_add y0 (real_add y1 x0)) = (real_add y1 (real_add y0 x0)))))) -> (forall y2 : real, forall y3 : real, (real_add y2 y3) = (real_add y3 y2)) -> (forall y2 : real, forall y3 : real, forall y4 : real, (real_add y2 (real_add y3 y4)) = (real_add (real_add y2 y3) y4)) -> False.
Definition term30 (x0 : real) (x1 : real) := fun y0 : real => (real_add x0 (real_add x1 y0)) = (real_add (real_add x0 x1) y0).
Definition term8 := (forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) -> False.
Definition term44 (x0 : real) (x1 : real) (x2 : real) := ((real_add (real_add x1 x0) x2) = (real_add x1 (real_add x0 x2))) /\ ((real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2))).
Definition term64 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term9 := ~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)).
Definition term31 (x0 : real) (x1 : real) := forall y0 : real, (real_add x0 (real_add x1 y0)) = (real_add (real_add x0 x1) y0).
Definition term63 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term14 (x0 : real) (x1 : real) (x2 : real) := imp (~ (((real_add x1 x0) = (real_add x0 x1)) /\ (((real_add (real_add x1 x0) x2) = (real_add x1 (real_add x0 x2))) /\ ((real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2)))))).
Definition term74 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term89 (x0 : real) (x1 : real) (x2 : real) := ((real_add (real_add x0 x1) x2) = (real_add x0 (real_add x1 x2))) -> False.
Definition term87 (x0 : real) (x1 : real) (x2 : real) := (((real_add x0 (real_add x1 x2)) = (real_add (real_add x0 x1) x2)) /\ ((real_add x0 (real_add x1 x2)) = (real_add x0 (real_add x1 x2)))) -> (real_add (real_add x0 x1) x2) = (real_add x0 (real_add x1 x2)).
Definition term5 (x0 : real) (x1 : real) (x2 : real) := ((~ (((real_add x1 x0) = (real_add x0 x1)) /\ (((real_add (real_add x1 x0) x2) = (real_add x1 (real_add x0 x2))) /\ ((real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2)))))) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) -> False) -> (~ (((real_add x1 x0) = (real_add x0 x1)) /\ (((real_add (real_add x1 x0) x2) = (real_add x1 (real_add x0 x2))) /\ ((real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2)))))) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) -> False.
Definition term86 (x0 : real) (x1 : real) (x2 : real) := ((real_add x0 (real_add x1 x2)) = (real_add (real_add x0 x1) x2)) /\ ((real_add x0 (real_add x1 x2)) = (real_add x0 (real_add x1 x2))).
Definition term102 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((real_add x0 x1) = (real_add x2 x3)))).
Definition term45 (x0 : real) (x1 : real) := ~ ((real_add x1 x0) = (real_add x0 x1)).
Definition term37 := fun y0 : real => forall y1 : real, (real_add y0 y1) = (real_add y1 y0).
Definition term32 (x0 : real) := fun y0 : real => forall y1 : real, (real_add x0 (real_add y0 y1)) = (real_add (real_add x0 y0) y1).
Definition term90 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x1 = x3) -> (real_add x0 x1) = (real_add x2 x3).
Definition term52 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_add x0 (real_add x1 y0)) = (real_add (real_add x0 x1) y0)) x2.
Definition term48 (x0 : real) := (fun y0 : real => forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) x0.
Definition term112 (x0 : real) (x1 : real) (x2 : real) := (x0 = x0) /\ ((real_add x2 x1) = (real_add x1 x2)).
Definition term42 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_add x1 x0) = (real_add x0 x1))) \/ (~ (((real_add (real_add x1 x0) x2) = (real_add x1 (real_add x0 x2))) /\ ((real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2))))).
Definition term117 (x0 : real) (x1 : real) (x2 : real) := (((real_add x0 (real_add x2 x1)) = (real_add (real_add x0 x2) x1)) /\ ((real_add x0 (real_add x2 x1)) = (real_add x0 (real_add x1 x2)))) -> (real_add (real_add x0 x2) x1) = (real_add x0 (real_add x1 x2)).
Definition term82 (x0 : real) (x1 : real) (x2 : real) := (x1 = x0) /\ (x1 = x2).
Definition term95 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_add (real_add x1 x2) x0) = (real_add x0 (real_add x1 x2)))) -> (real_add (real_add x1 x2) x0) = (real_add x0 (real_add x1 x2)).
Definition term3 (x0 : real) (x1 : real) (x2 : real) := ~ (((real_add x1 x0) = (real_add x0 x1)) /\ (((real_add (real_add x1 x0) x2) = (real_add x1 (real_add x0 x2))) /\ ((real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2))))).
Definition term68 (x0 : real) (x1 : real) (x2 : real) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term66 (x0 : real) (x1 : real) (x2 : real) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term7 (x0 : real) (x1 : real) (x2 : real) := (((~ (((real_add x1 x0) = (real_add x0 x1)) /\ (((real_add (real_add x1 x0) x2) = (real_add x1 (real_add x0 x2))) /\ ((real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2)))))) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) -> False) -> (~ (((real_add x1 x0) = (real_add x0 x1)) /\ (((real_add (real_add x1 x0) x2) = (real_add x1 (real_add x0 x2))) /\ ((real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2)))))) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) -> False) -> ((~ (((real_add x1 x0) = (real_add x0 x1)) /\ (((real_add (real_add x1 x0) x2) = (real_add x1 (real_add x0 x2))) /\ ((real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2)))))) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) -> False) -> (~ (((real_add x1 x0) = (real_add x0 x1)) /\ (((real_add (real_add x1 x0) x2) = (real_add x1 (real_add x0 x2))) /\ ((real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2)))))) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) -> False.
Definition term53 (x0 : real) (x1 : real) := (~ ((real_add x1 x0) = (real_add x0 x1))) -> (real_add x1 x0) = (real_add x0 x1).
Definition term125 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (~ (((real_add y0 y1) = (real_add y1 y0)) /\ (((real_add (real_add y0 y1) x0) = (real_add y0 (real_add y1 x0))) /\ ((real_add y0 (real_add y1 x0)) = (real_add y1 (real_add y0 x0)))))) -> (forall y2 : real, forall y3 : real, (real_add y2 y3) = (real_add y3 y2)) -> (forall y2 : real, forall y3 : real, forall y4 : real, (real_add y2 (real_add y3 y4)) = (real_add (real_add y2 y3) y4)) -> False) x1.
Definition term51 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_add x0 (real_add y0 y1)) = (real_add (real_add x0 y0) y1)) x1.
Definition term80 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term55 (x0 : real) (x1 : real) := ((real_add x1 x0) = (real_add x0 x1)) -> False.
Definition term28 (x0 : real) (x1 : real) (x2 : real) := real_add x0 (real_add x1 x2).
Definition term17 (x0 : real) (x1 : real) := fun y0 : real => (~ (((real_add x0 y0) = (real_add y0 x0)) /\ (((real_add (real_add x0 y0) x1) = (real_add x0 (real_add y0 x1))) /\ ((real_add x0 (real_add y0 x1)) = (real_add y0 (real_add x0 x1)))))) -> (forall y1 : real, forall y2 : real, (real_add y1 y2) = (real_add y2 y1)) -> ~ (forall y1 : real, forall y2 : real, forall y3 : real, (real_add y1 (real_add y2 y3)) = (real_add (real_add y1 y2) y3)).
Definition term111 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((x0 = x2) /\ (x1 = x3)) -> (real_add x0 x1) = (real_add x2 x3).
Definition term100 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x0 = x1)) \/ (((real_add x0 x2) = (real_add x1 x3)) \/ (~ (x2 = x3))).
Definition term34 := fun y0 : real => forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2).
Definition term25 := fun y0 : real => forall y1 : real, forall y2 : real, (~ (((real_add y1 y2) = (real_add y2 y1)) /\ (((real_add (real_add y1 y2) y0) = (real_add y1 (real_add y2 y0))) /\ ((real_add y1 (real_add y2 y0)) = (real_add y2 (real_add y1 y0)))))) -> (forall y3 : real, forall y4 : real, (real_add y3 y4) = (real_add y4 y3)) -> ~ (forall y3 : real, forall y4 : real, forall y5 : real, (real_add y3 (real_add y4 y5)) = (real_add (real_add y3 y4) y5)).
Definition term24 := fun y0 : real => forall y1 : real, forall y2 : real, (~ (((real_add y1 y2) = (real_add y2 y1)) /\ (((real_add (real_add y1 y2) y0) = (real_add y1 (real_add y2 y0))) /\ ((real_add y1 (real_add y2 y0)) = (real_add y2 (real_add y1 y0)))))) -> (forall y3 : real, forall y4 : real, (real_add y3 y4) = (real_add y4 y3)) -> (forall y3 : real, forall y4 : real, forall y5 : real, (real_add y3 (real_add y4 y5)) = (real_add (real_add y3 y4) y5)) -> False.
Definition term1 (x0 : real) (x1 : real) (x2 : real) := ((real_add x1 x0) = (real_add x0 x1)) /\ (((real_add (real_add x1 x0) x2) = (real_add x1 (real_add x0 x2))) /\ ((real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2)))).
Definition term99 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_add x0 x2) = (real_add x1 x3)) \/ (~ (x2 = x3)).
Definition term41 (x0 : real) (x1 : real) := or (~ ((real_add x1 x0) = (real_add x0 x1))).
Definition term108 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x0 = x1) /\ (x2 = x3).
Definition term85 (x0 : real) (x1 : real) (x2 : real) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term106 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ~ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term76 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term72 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term81 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term13 := (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> ~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)).
Definition term39 (x0 : real) (x1 : real) (x2 : real) := ~ (((real_add (real_add x1 x0) x2) = (real_add x1 (real_add x0 x2))) /\ ((real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2)))).
Definition term91 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term98 (x0 : real) := ~ (x0 = x0).
Definition term105 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x0 = x1)) \/ (~ (x2 = x3)).
Definition term94 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((real_add x0 x1) = (real_add x2 x3))).
Definition term84 (x0 : real) (x1 : real) (x2 : real) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term92 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x1 = x3)) \/ ((real_add x0 x1) = (real_add x2 x3)).
Definition term15 (x0 : real) (x1 : real) (x2 : real) := (~ (((real_add x1 x0) = (real_add x0 x1)) /\ (((real_add (real_add x1 x0) x2) = (real_add x1 (real_add x0 x2))) /\ ((real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2)))))) -> (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) -> ~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)).
Definition term113 (x0 : real) (x1 : real) (x2 : real) := ((x0 = x0) /\ ((real_add x2 x1) = (real_add x1 x2))) -> (real_add x0 (real_add x2 x1)) = (real_add x0 (real_add x1 x2)).
Definition term120 (x0 : real) (x1 : real) (x2 : real) := ((real_add (real_add x0 x2) x1) = (real_add x1 (real_add x0 x2))) /\ ((real_add (real_add x0 x2) x1) = (real_add x0 (real_add x1 x2))).
Definition term62 (x0 : real) (x1 : real) (x2 : real) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term79 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term29 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add x0 x1) x2.
Definition term65 (x0 : real) (x1 : real) := or (~ (x0 = x1)).
Definition term124 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (~ (((real_add y1 y2) = (real_add y2 y1)) /\ (((real_add (real_add y1 y2) y0) = (real_add y1 (real_add y2 y0))) /\ ((real_add y1 (real_add y2 y0)) = (real_add y2 (real_add y1 y0)))))) -> (forall y3 : real, forall y4 : real, (real_add y3 y4) = (real_add y4 y3)) -> (forall y3 : real, forall y4 : real, forall y5 : real, (real_add y3 (real_add y4 y5)) = (real_add (real_add y3 y4) y5)) -> False) x0.
Definition term50 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) x0.
Definition term122 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2)))) -> (real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2)).
Definition term114 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_add x0 (real_add x2 x1)) = (real_add x0 (real_add x1 x2)))) -> (real_add x0 (real_add x2 x1)) = (real_add x0 (real_add x1 x2)).
Definition term60 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_add x0 (real_add x1 x2)) = (real_add x0 (real_add x1 x2)))) -> (real_add x0 (real_add x1 x2)) = (real_add x0 (real_add x1 x2)).
Definition term16 (x0 : real) (x1 : real) := fun y0 : real => (~ (((real_add x0 y0) = (real_add y0 x0)) /\ (((real_add (real_add x0 y0) x1) = (real_add x0 (real_add y0 x1))) /\ ((real_add x0 (real_add y0 x1)) = (real_add y0 (real_add x0 x1)))))) -> (forall y1 : real, forall y2 : real, (real_add y1 y2) = (real_add y2 y1)) -> (forall y1 : real, forall y2 : real, forall y3 : real, (real_add y1 (real_add y2 y3)) = (real_add (real_add y1 y2) y3)) -> False.
