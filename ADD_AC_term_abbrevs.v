Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term64 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term112 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x0) /\ ((Nat.add x2 x1) = (Nat.add x1 x2)).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := (((~ (((Nat.add x1 x0) = (Nat.add x0 x1)) /\ (((Nat.add (Nat.add x1 x0) x2) = (Nat.add x1 (Nat.add x0 x2))) /\ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2)))))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)) -> False) -> (~ (((Nat.add x1 x0) = (Nat.add x0 x1)) /\ (((Nat.add (Nat.add x1 x0) x2) = (Nat.add x1 (Nat.add x0 x2))) /\ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2)))))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)) -> False) -> (~ (((Nat.add x1 x0) = (Nat.add x0 x1)) /\ (((Nat.add (Nat.add x1 x0) x2) = (Nat.add x1 (Nat.add x0 x2))) /\ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2)))))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)) -> False.
Definition term56 := (~ False) -> False.
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term35 (x0 : nat) := fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term108 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = x1) /\ (x2 = x3).
Definition term78 (x0 : Prop) := ~ (~ x0).
Definition term124 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (((Nat.add y1 y2) = (Nat.add y2 y1)) /\ (((Nat.add (Nat.add y1 y2) y0) = (Nat.add y1 (Nat.add y2 y0))) /\ ((Nat.add y1 (Nat.add y2 y0)) = (Nat.add y2 (Nat.add y1 y0)))))) -> (forall y3 : nat, forall y4 : nat, (Nat.add y3 y4) = (Nat.add y4 y3)) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, (Nat.add y3 (Nat.add y4 y5)) = (Nat.add (Nat.add y3 y4) y5)) -> False) x0.
Definition term50 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)) x0.
Definition term53 (x0 : nat) (x1 : nat) := (~ ((Nat.add x1 x0) = (Nat.add x0 x1))) -> (Nat.add x1 x0) = (Nat.add x0 x1).
Definition term92 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x3)) \/ ((Nat.add x0 x1) = (Nat.add x2 x3)).
Definition term107 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (~ (x0 = x1))) /\ (~ (~ (x2 = x3))).
Definition term77 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term103 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop (((Nat.add x0 x2) = (Nat.add x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term95 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.add (Nat.add x1 x2) x0) = (Nat.add x0 (Nat.add x1 x2)))) -> (Nat.add (Nat.add x1 x2) x0) = (Nat.add x0 (Nat.add x1 x2)).
Definition term98 (x0 : nat) := ~ (x0 = x0).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term109 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp (~ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term83 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term2 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (((Nat.add x1 x0) = (Nat.add x0 x1)) /\ (((Nat.add (Nat.add x1 x0) x2) = (Nat.add x1 (Nat.add x0 x2))) /\ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2)))))) -> False.
Definition term123 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2))) -> False.
Definition term113 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = x0) /\ ((Nat.add x2 x1) = (Nat.add x1 x2))) -> (Nat.add x0 (Nat.add x2 x1)) = (Nat.add x0 (Nat.add x1 x2)).
Definition term18 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (((Nat.add x0 y0) = (Nat.add y0 x0)) /\ (((Nat.add (Nat.add x0 y0) x1) = (Nat.add x0 (Nat.add y0 x1))) /\ ((Nat.add x0 (Nat.add y0 x1)) = (Nat.add y0 (Nat.add x0 x1)))))) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, (Nat.add y1 (Nat.add y2 y3)) = (Nat.add (Nat.add y1 y2) y3)) -> False.
Definition term71 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term81 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term9 := ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term54 (x0 : Prop) := (~ x0) -> x0.
Definition term82 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = x0) /\ (x1 = x2).
Definition term119 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Nat.add (Nat.add x0 x2) x1) = (Nat.add x0 (Nat.add x1 x2))).
Definition term110 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((x0 = x1) /\ (x2 = x3)).
Definition term17 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (((Nat.add x0 y0) = (Nat.add y0 x0)) /\ (((Nat.add (Nat.add x0 y0) x1) = (Nat.add x0 (Nat.add y0 x1))) /\ ((Nat.add x0 (Nat.add y0 x1)) = (Nat.add y0 (Nat.add x0 x1)))))) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> ~ (forall y1 : nat, forall y2 : nat, forall y3 : nat, (Nat.add y1 (Nat.add y2 y3)) = (Nat.add (Nat.add y1 y2) y3)).
Definition term111 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x0 = x2) /\ (x1 = x3)) -> (Nat.add x0 x1) = (Nat.add x2 x3).
Definition term30 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term73 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.add (Nat.add x1 x0) x2) = (Nat.add x1 (Nat.add x0 x2)))) \/ (~ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2)))).
Definition term75 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term115 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Nat.add x0 (Nat.add x2 x1)) = (Nat.add x0 (Nat.add x1 x2))).
Definition term61 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Nat.add x0 (Nat.add x1 x2)) = (Nat.add x0 (Nat.add x1 x2))).
Definition term47 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2))).
Definition term97 (x0 : nat) := (~ (x0 = x0)) -> x0 = x0.
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term31 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term12 := (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)) -> False.
Definition term67 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term43 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.add x1 x0) = (Nat.add x0 x1))) \/ ((~ ((Nat.add (Nat.add x1 x0) x2) = (Nat.add x1 (Nat.add x0 x2)))) \/ (~ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2))))).
Definition term125 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (((Nat.add y0 y1) = (Nat.add y1 y0)) /\ (((Nat.add (Nat.add y0 y1) x0) = (Nat.add y0 (Nat.add y1 x0))) /\ ((Nat.add y0 (Nat.add y1 x0)) = (Nat.add y1 (Nat.add y0 x0)))))) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, (Nat.add y2 (Nat.add y3 y4)) = (Nat.add (Nat.add y2 y3) y4)) -> False) x1.
Definition term51 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1)) x1.
Definition term101 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.add x0 x2) = (Nat.add x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term37 := fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0).
Definition term32 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term99 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.add x0 x2) = (Nat.add x1 x3)) \/ (~ (x2 = x3)).
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (((Nat.add x1 x0) = (Nat.add x0 x1)) /\ (((Nat.add (Nat.add x1 x0) x2) = (Nat.add x1 (Nat.add x0 x2))) /\ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2)))))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)) -> False.
Definition term19 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (((Nat.add x0 y0) = (Nat.add y0 x0)) /\ (((Nat.add (Nat.add x0 y0) x1) = (Nat.add x0 (Nat.add y0 x1))) /\ ((Nat.add x0 (Nat.add y0 x1)) = (Nat.add y0 (Nat.add x0 x1)))))) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> ~ (forall y1 : nat, forall y2 : nat, forall y3 : nat, (Nat.add y1 (Nat.add y2 y3)) = (Nat.add (Nat.add y1 y2) y3)).
Definition term57 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term16 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (((Nat.add x0 y0) = (Nat.add y0 x0)) /\ (((Nat.add (Nat.add x0 y0) x1) = (Nat.add x0 (Nat.add y0 x1))) /\ ((Nat.add x0 (Nat.add y0 x1)) = (Nat.add y0 (Nat.add x0 x1)))))) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, (Nat.add y1 (Nat.add y2 y3)) = (Nat.add (Nat.add y1 y2) y3)) -> False.
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term58 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.add x0 (Nat.add x1 x2)) = (Nat.add (Nat.add x0 x1) x2))) -> (Nat.add x0 (Nat.add x1 x2)) = (Nat.add (Nat.add x0 x1) x2).
Definition term8 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)) -> False.
Definition term126 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (((Nat.add x0 y0) = (Nat.add y0 x0)) /\ (((Nat.add (Nat.add x0 y0) x1) = (Nat.add x0 (Nat.add y0 x1))) /\ ((Nat.add x0 (Nat.add y0 x1)) = (Nat.add y0 (Nat.add x0 x1)))))) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, (Nat.add y1 (Nat.add y2 y3)) = (Nat.add (Nat.add y1 y2) y3)) -> False) x2.
Definition term104 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((~ (x0 = x2)) \/ (~ (x1 = x3)))) -> (Nat.add x0 x1) = (Nat.add x2 x3).
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ (((Nat.add x1 x0) = (Nat.add x0 x1)) /\ (((Nat.add (Nat.add x1 x0) x2) = (Nat.add x1 (Nat.add x0 x2))) /\ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2)))))).
Definition term96 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Nat.add (Nat.add x1 x2) x0) = (Nat.add x0 (Nat.add x1 x2))).
Definition term74 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term38 := forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0).
Definition term33 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term27 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (((Nat.add y1 y2) = (Nat.add y2 y1)) /\ (((Nat.add (Nat.add y1 y2) y0) = (Nat.add y1 (Nat.add y2 y0))) /\ ((Nat.add y1 (Nat.add y2 y0)) = (Nat.add y2 (Nat.add y1 y0)))))) -> (forall y3 : nat, forall y4 : nat, (Nat.add y3 y4) = (Nat.add y4 y3)) -> ~ (forall y3 : nat, forall y4 : nat, forall y5 : nat, (Nat.add y3 (Nat.add y4 y5)) = (Nat.add (Nat.add y3 y4) y5)).
Definition term26 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (((Nat.add y1 y2) = (Nat.add y2 y1)) /\ (((Nat.add (Nat.add y1 y2) y0) = (Nat.add y1 (Nat.add y2 y0))) /\ ((Nat.add y1 (Nat.add y2 y0)) = (Nat.add y2 (Nat.add y1 y0)))))) -> (forall y3 : nat, forall y4 : nat, (Nat.add y3 y4) = (Nat.add y4 y3)) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, (Nat.add y3 (Nat.add y4 y5)) = (Nat.add (Nat.add y3 y4) y5)) -> False.
Definition term23 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (((Nat.add y0 y1) = (Nat.add y1 y0)) /\ (((Nat.add (Nat.add y0 y1) x0) = (Nat.add y0 (Nat.add y1 x0))) /\ ((Nat.add y0 (Nat.add y1 x0)) = (Nat.add y1 (Nat.add y0 x0)))))) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> ~ (forall y2 : nat, forall y3 : nat, forall y4 : nat, (Nat.add y2 (Nat.add y3 y4)) = (Nat.add (Nat.add y2 y3) y4)).
Definition term22 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (((Nat.add y0 y1) = (Nat.add y1 y0)) /\ (((Nat.add (Nat.add y0 y1) x0) = (Nat.add y0 (Nat.add y1 x0))) /\ ((Nat.add y0 (Nat.add y1 x0)) = (Nat.add y1 (Nat.add y0 x0)))))) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, (Nat.add y2 (Nat.add y3 y4)) = (Nat.add (Nat.add y2 y3) y4)) -> False.
Definition term10 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2).
Definition term88 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.add (Nat.add x0 x1) x2) = (Nat.add x0 (Nat.add x1 x2)))) -> (Nat.add (Nat.add x0 x1) x2) = (Nat.add x0 (Nat.add x1 x2)).
Definition term89 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add (Nat.add x0 x1) x2) = (Nat.add x0 (Nat.add x1 x2))) -> False.
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (((Nat.add x1 x0) = (Nat.add x0 x1)) /\ (((Nat.add (Nat.add x1 x0) x2) = (Nat.add x1 (Nat.add x0 x2))) /\ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2)))))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)) -> False) -> (~ (((Nat.add x1 x0) = (Nat.add x0 x1)) /\ (((Nat.add (Nat.add x1 x0) x2) = (Nat.add x1 (Nat.add x0 x2))) /\ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2)))))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)) -> False.
Definition term102 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((Nat.add x0 x1) = (Nat.add x2 x3)))).
Definition term44 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add (Nat.add x1 x0) x2) = (Nat.add x1 (Nat.add x0 x2))) /\ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2))).
Definition term90 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x1 = x3) -> (Nat.add x0 x1) = (Nat.add x2 x3).
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.add x1 x0) = (Nat.add x0 x1))) \/ (~ (((Nat.add (Nat.add x1 x0) x2) = (Nat.add x1 (Nat.add x0 x2))) /\ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2))))).
Definition term87 (x0 : nat) (x1 : nat) (x2 : nat) := (((Nat.add x0 (Nat.add x1 x2)) = (Nat.add (Nat.add x0 x1) x2)) /\ ((Nat.add x0 (Nat.add x1 x2)) = (Nat.add x0 (Nat.add x1 x2)))) -> (Nat.add (Nat.add x0 x1) x2) = (Nat.add x0 (Nat.add x1 x2)).
Definition term63 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term120 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add (Nat.add x0 x2) x1) = (Nat.add x1 (Nat.add x0 x2))) /\ ((Nat.add (Nat.add x0 x2) x1) = (Nat.add x0 (Nat.add x1 x2))).
Definition term116 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add x0 (Nat.add x2 x1)) = (Nat.add (Nat.add x0 x2) x1)) /\ ((Nat.add x0 (Nat.add x2 x1)) = (Nat.add x0 (Nat.add x1 x2))).
Definition term36 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term3 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (((Nat.add x1 x0) = (Nat.add x0 x1)) /\ (((Nat.add (Nat.add x1 x0) x2) = (Nat.add x1 (Nat.add x0 x2))) /\ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2))))).
Definition term66 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) := (((~ (((Nat.add x1 x0) = (Nat.add x0 x1)) /\ (((Nat.add (Nat.add x1 x0) x2) = (Nat.add x1 (Nat.add x0 x2))) /\ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2)))))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)) -> False) -> (~ (((Nat.add x1 x0) = (Nat.add x0 x1)) /\ (((Nat.add (Nat.add x1 x0) x2) = (Nat.add x1 (Nat.add x0 x2))) /\ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2)))))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)) -> False) -> ((~ (((Nat.add x1 x0) = (Nat.add x0 x1)) /\ (((Nat.add (Nat.add x1 x0) x2) = (Nat.add x1 (Nat.add x0 x2))) /\ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2)))))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)) -> False) -> (~ (((Nat.add x1 x0) = (Nat.add x0 x1)) /\ (((Nat.add (Nat.add x1 x0) x2) = (Nat.add x1 (Nat.add x0 x2))) /\ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2)))))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)) -> False.
Definition term49 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0)) x1.
Definition term80 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term55 (x0 : nat) (x1 : nat) := ((Nat.add x1 x0) = (Nat.add x0 x1)) -> False.
Definition term100 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x1)) \/ (((Nat.add x0 x2) = (Nat.add x1 x3)) \/ (~ (x2 = x3))).
Definition term48 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) x0.
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add x1 x0) = (Nat.add x0 x1)) /\ (((Nat.add (Nat.add x1 x0) x2) = (Nat.add x1 (Nat.add x0 x2))) /\ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2)))).
Definition term121 (x0 : nat) (x1 : nat) (x2 : nat) := (((Nat.add (Nat.add x0 x2) x1) = (Nat.add x1 (Nat.add x0 x2))) /\ ((Nat.add (Nat.add x0 x2) x1) = (Nat.add x0 (Nat.add x1 x2)))) -> (Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2)).
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0)) x2.
Definition term41 (x0 : nat) (x1 : nat) := or (~ ((Nat.add x1 x0) = (Nat.add x0 x1))).
Definition term59 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Nat.add x0 (Nat.add x1 x2)) = (Nat.add (Nat.add x0 x1) x2)).
Definition term106 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term93 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = x2) -> (~ (x1 = x3)) \/ ((Nat.add x0 x1) = (Nat.add x2 x3)).
Definition term86 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add x0 (Nat.add x1 x2)) = (Nat.add (Nat.add x0 x1) x2)) /\ ((Nat.add x0 (Nat.add x1 x2)) = (Nat.add x0 (Nat.add x1 x2))).
Definition term122 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2)))) -> (Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2)).
Definition term114 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.add x0 (Nat.add x2 x1)) = (Nat.add x0 (Nat.add x1 x2)))) -> (Nat.add x0 (Nat.add x2 x1)) = (Nat.add x0 (Nat.add x1 x2)).
Definition term60 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.add x0 (Nat.add x1 x2)) = (Nat.add x0 (Nat.add x1 x2)))) -> (Nat.add x0 (Nat.add x1 x2)) = (Nat.add x0 (Nat.add x1 x2)).
Definition term13 := (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)).
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (((Nat.add (Nat.add x1 x0) x2) = (Nat.add x1 (Nat.add x0 x2))) /\ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2)))).
Definition term91 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term105 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x1)) \/ (~ (x2 = x3)).
Definition term45 (x0 : nat) (x1 : nat) := ~ ((Nat.add x1 x0) = (Nat.add x0 x1)).
Definition term46 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Nat.add (Nat.add x0 x1) x2) = (Nat.add x0 (Nat.add x1 x2))).
Definition term94 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((Nat.add x0 x1) = (Nat.add x2 x3))).
Definition term84 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (((Nat.add x1 x0) = (Nat.add x0 x1)) /\ (((Nat.add (Nat.add x1 x0) x2) = (Nat.add x1 (Nat.add x0 x2))) /\ ((Nat.add x1 (Nat.add x0 x2)) = (Nat.add x0 (Nat.add x1 x2)))))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)).
Definition term62 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term79 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term118 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.add (Nat.add x0 x2) x1) = (Nat.add x0 (Nat.add x1 x2)))) -> (Nat.add (Nat.add x0 x2) x1) = (Nat.add x0 (Nat.add x1 x2)).
Definition term65 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term11 := imp (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)).
Definition term117 (x0 : nat) (x1 : nat) (x2 : nat) := (((Nat.add x0 (Nat.add x2 x1)) = (Nat.add (Nat.add x0 x2) x1)) /\ ((Nat.add x0 (Nat.add x2 x1)) = (Nat.add x0 (Nat.add x1 x2)))) -> (Nat.add (Nat.add x0 x2) x1) = (Nat.add x0 (Nat.add x1 x2)).
Definition term85 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term21 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (((Nat.add y0 y1) = (Nat.add y1 y0)) /\ (((Nat.add (Nat.add y0 y1) x0) = (Nat.add y0 (Nat.add y1 x0))) /\ ((Nat.add y0 (Nat.add y1 x0)) = (Nat.add y1 (Nat.add y0 x0)))))) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> ~ (forall y2 : nat, forall y3 : nat, forall y4 : nat, (Nat.add y2 (Nat.add y3 y4)) = (Nat.add (Nat.add y2 y3) y4)).
Definition term20 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (((Nat.add y0 y1) = (Nat.add y1 y0)) /\ (((Nat.add (Nat.add y0 y1) x0) = (Nat.add y0 (Nat.add y1 x0))) /\ ((Nat.add y0 (Nat.add y1 x0)) = (Nat.add y1 (Nat.add y0 x0)))))) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, (Nat.add y2 (Nat.add y3 y4)) = (Nat.add (Nat.add y2 y3) y4)) -> False.
Definition term34 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2).
Definition term25 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (((Nat.add y1 y2) = (Nat.add y2 y1)) /\ (((Nat.add (Nat.add y1 y2) y0) = (Nat.add y1 (Nat.add y2 y0))) /\ ((Nat.add y1 (Nat.add y2 y0)) = (Nat.add y2 (Nat.add y1 y0)))))) -> (forall y3 : nat, forall y4 : nat, (Nat.add y3 y4) = (Nat.add y4 y3)) -> ~ (forall y3 : nat, forall y4 : nat, forall y5 : nat, (Nat.add y3 (Nat.add y4 y5)) = (Nat.add (Nat.add y3 y4) y5)).
Definition term24 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (((Nat.add y1 y2) = (Nat.add y2 y1)) /\ (((Nat.add (Nat.add y1 y2) y0) = (Nat.add y1 (Nat.add y2 y0))) /\ ((Nat.add y1 (Nat.add y2 y0)) = (Nat.add y2 (Nat.add y1 y0)))))) -> (forall y3 : nat, forall y4 : nat, (Nat.add y3 y4) = (Nat.add y4 y3)) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, (Nat.add y3 (Nat.add y4 y5)) = (Nat.add (Nat.add y3 y4) y5)) -> False.
