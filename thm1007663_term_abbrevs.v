Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term34 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL y0))) (Nat.mul x0 x1).
Definition term47 (x0 : nat) (x1 : nat) := (~ ((NUMERAL (Nat.mul (NUMERAL x0) (NUMERAL x1))) = (Nat.mul (NUMERAL x0) (NUMERAL x1)))) -> (NUMERAL (Nat.mul (NUMERAL x0) (NUMERAL x1))) = (Nat.mul (NUMERAL x0) (NUMERAL x1)).
Definition term113 (x0 : nat) (x1 : nat) (x2 : nat) := ((NUMERAL x2) = (Nat.mul x0 x1)) /\ ((NUMERAL x2) = x2).
Definition term53 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term107 := (~ False) -> False.
Definition term95 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (~ ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL x2))).
Definition term104 (x0 : nat) (x1 : nat) := (((NUMERAL (Nat.mul (NUMERAL x0) (NUMERAL x1))) = (Nat.mul (NUMERAL x0) (NUMERAL x1))) /\ ((NUMERAL (Nat.mul (NUMERAL x0) (NUMERAL x1))) = (NUMERAL (Nat.mul x0 x1)))) -> (Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL (Nat.mul x0 x1)).
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = x1) /\ (x2 = x3).
Definition term67 (x0 : Prop) := ~ (~ x0).
Definition term117 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (((Nat.mul y2 y1) = y0) = ((Nat.mul (NUMERAL y2) (NUMERAL y1)) = (NUMERAL y0)))) -> (forall y3 : nat, (NUMERAL y3) = y3) -> False) x0.
Definition term86 (x0 : nat) (x1 : nat) := NUMERAL (Nat.mul x0 x1).
Definition term43 (x0 : nat) (x1 : nat) := (x0 = x1) -> (NUMERAL x0) = (NUMERAL x1).
Definition term109 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.mul (NUMERAL x1) (NUMERAL x2)) = (NUMERAL x0)) /\ ((Nat.mul (NUMERAL x1) (NUMERAL x2)) = (Nat.mul x1 x2)).
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ (((Nat.mul x0 x1) = x2) = ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL x2)))).
Definition term66 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (~ (x0 = x1))) /\ (~ (~ (x2 = x3))).
Definition term108 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL x2))) -> (Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL x2).
Definition term98 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term59 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop (((Nat.mul x0 x2) = (Nat.mul x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term8 := (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := (((~ (((Nat.mul x0 x1) = x2) = ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL x2)))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ (((Nat.mul x0 x1) = x2) = ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL x2)))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ (((Nat.mul x0 x1) = x2) = ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL x2)))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term100 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp (~ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term2 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (((Nat.mul x0 x1) = x2) = ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL x2)))) -> False.
Definition term103 (x0 : nat) (x1 : nat) := ((NUMERAL (Nat.mul (NUMERAL x0) (NUMERAL x1))) = (Nat.mul (NUMERAL x0) (NUMERAL x1))) /\ ((NUMERAL (Nat.mul (NUMERAL x0) (NUMERAL x1))) = (NUMERAL (Nat.mul x0 x1))).
Definition term35 (x0 : nat) (x1 : nat) := ~ ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL (Nat.mul x0 x1))).
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (((Nat.mul x0 x1) = x2) = ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL x2)))) -> ~ (forall y0 : nat, (NUMERAL y0) = y0).
Definition term60 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term32 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL y0)).
Definition term70 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term110 (x0 : nat) (x1 : nat) (x2 : nat) := (((Nat.mul (NUMERAL x1) (NUMERAL x2)) = (NUMERAL x0)) /\ ((Nat.mul (NUMERAL x1) (NUMERAL x2)) = (Nat.mul x1 x2))) -> (NUMERAL x0) = (Nat.mul x1 x2).
Definition term49 (x0 : Prop) := (~ x0) -> x0.
Definition term99 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = x0) /\ (x1 = x2).
Definition term73 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((x0 = x1) /\ (x2 = x3)).
Definition term96 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term50 (x0 : nat) := (~ ((NUMERAL x0) = x0)) -> (NUMERAL x0) = x0.
Definition term64 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term93 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term31 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Nat.mul x0 x1) = x2).
Definition term94 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term116 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.mul x0 x1) = x2) -> False.
Definition term56 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term118 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (((Nat.mul y1 y0) = x0) = ((Nat.mul (NUMERAL y1) (NUMERAL y0)) = (NUMERAL x0)))) -> (forall y2 : nat, (NUMERAL y2) = y2) -> False) x1.
Definition term87 (x0 : nat) (x1 : nat) := (~ ((NUMERAL (Nat.mul (NUMERAL x0) (NUMERAL x1))) = (NUMERAL (Nat.mul x0 x1)))) -> (NUMERAL (Nat.mul (NUMERAL x0) (NUMERAL x1))) = (NUMERAL (Nat.mul x0 x1)).
Definition term111 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((NUMERAL x0) = (Nat.mul x1 x2))) -> (NUMERAL x0) = (Nat.mul x1 x2).
Definition term57 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.mul x0 x2) = (Nat.mul x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term81 (x0 : nat) (x1 : nat) := @eq Prop (((NUMERAL x0) = (NUMERAL x1)) \/ (~ (x0 = x1))).
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.mul x0 x2) = (Nat.mul x1 x3)) \/ (~ (x2 = x3)).
Definition term14 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (((Nat.mul y0 x0) = x1) = ((Nat.mul (NUMERAL y0) (NUMERAL x0)) = (NUMERAL x1)))) -> ~ (forall y1 : nat, (NUMERAL y1) = y1).
Definition term105 (x0 : nat) (x1 : nat) := (~ ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL (Nat.mul x0 x1)))) -> (Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL (Nat.mul x0 x1)).
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (((Nat.mul x0 x1) = x2) = ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL x2)))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term115 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.mul x0 x1) = x2)) -> (Nat.mul x0 x1) = x2.
Definition term3 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (((Nat.mul x0 x1) = x2) = ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL x2))).
Definition term45 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term48 (x0 : nat) (x1 : nat) := ~ ((NUMERAL (Nat.mul (NUMERAL x0) (NUMERAL x1))) = (Nat.mul (NUMERAL x0) (NUMERAL x1))).
Definition term92 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term75 (x0 : nat) (x1 : nat) := ((NUMERAL x0) = x0) /\ ((NUMERAL x1) = x1).
Definition term84 (x0 : nat) (x1 : nat) := imp (x0 = x1).
Definition term29 (x0 : nat) := (fun y0 : nat => (NUMERAL y0) = y0) x0.
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.mul x0 x1) = x2) /\ (~ ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL x2))).
Definition term63 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term24 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (((Nat.mul y2 y1) = y0) = ((Nat.mul (NUMERAL y2) (NUMERAL y1)) = (NUMERAL y0)))) -> ~ (forall y3 : nat, (NUMERAL y3) = y3).
Definition term23 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (((Nat.mul y2 y1) = y0) = ((Nat.mul (NUMERAL y2) (NUMERAL y1)) = (NUMERAL y0)))) -> (forall y3 : nat, (NUMERAL y3) = y3) -> False.
Definition term20 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (((Nat.mul y1 y0) = x0) = ((Nat.mul (NUMERAL y1) (NUMERAL y0)) = (NUMERAL x0)))) -> ~ (forall y2 : nat, (NUMERAL y2) = y2).
Definition term19 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (((Nat.mul y1 y0) = x0) = ((Nat.mul (NUMERAL y1) (NUMERAL y0)) = (NUMERAL x0)))) -> (forall y2 : nat, (NUMERAL y2) = y2) -> False.
Definition term58 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((Nat.mul x0 x1) = (Nat.mul x2 x3)))).
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x1 = x3) -> (Nat.mul x0 x1) = (Nat.mul x2 x3).
Definition term10 := forall y0 : nat, (NUMERAL y0) = y0.
Definition term90 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term77 (x0 : nat) (x1 : nat) := (~ ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (Nat.mul x0 x1))) -> (Nat.mul (NUMERAL x0) (NUMERAL x1)) = (Nat.mul x0 x1).
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL x2)).
Definition term1 (x0 : nat) (x1 : nat) := Nat.mul (NUMERAL x0) (NUMERAL x1).
Definition term106 (x0 : nat) (x1 : nat) := ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL (Nat.mul x0 x1))) -> False.
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x0 = x2) /\ (x1 = x3)) -> (Nat.mul x0 x1) = (Nat.mul x2 x3).
Definition term78 (x0 : nat) (x1 : nat) := ~ ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (Nat.mul x0 x1)).
Definition term91 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term15 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (((Nat.mul y0 x0) = x1) = ((Nat.mul (NUMERAL y0) (NUMERAL x0)) = (NUMERAL x1)))) -> (forall y1 : nat, (NUMERAL y1) = y1) -> False.
Definition term69 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term80 (x0 : nat) (x1 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((NUMERAL x0) = (NUMERAL x1))).
Definition term46 (x0 : nat) (x1 : nat) := NUMERAL (Nat.mul (NUMERAL x0) (NUMERAL x1)).
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : nat => ~ ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL y0))) x2).
Definition term55 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x1)) \/ (((Nat.mul x0 x2) = (Nat.mul x1 x3)) \/ (~ (x2 = x3))).
Definition term76 (x0 : nat) (x1 : nat) := (((NUMERAL x0) = x0) /\ ((NUMERAL x1) = x1)) -> (Nat.mul (NUMERAL x0) (NUMERAL x1)) = (Nat.mul x0 x1).
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (((Nat.mul x0 x1) = x2) = ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL x2)))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ (((Nat.mul x0 x1) = x2) = ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL x2)))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term114 (x0 : nat) (x1 : nat) (x2 : nat) := (((NUMERAL x2) = (Nat.mul x0 x1)) /\ ((NUMERAL x2) = x2)) -> (Nat.mul x0 x1) = x2.
Definition term97 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term65 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term41 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = x2) -> (~ (x1 = x3)) \/ ((Nat.mul x0 x1) = (Nat.mul x2 x3)).
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := (((Nat.mul x0 x1) = x2) /\ (~ ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL x2)))) \/ ((~ ((Nat.mul x0 x1) = x2)) /\ ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL x2))).
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.mul x0 x1) = x2)) /\ ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL x2)).
Definition term39 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term62 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x1)) \/ (~ (x2 = x3)).
Definition term61 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((~ (x0 = x2)) \/ (~ (x1 = x3)))) -> (Nat.mul x0 x1) = (Nat.mul x2 x3).
Definition term25 := fun y0 : nat => (NUMERAL y0) = y0.
Definition term79 (x0 : nat) (x1 : nat) := ((NUMERAL x0) = (NUMERAL x1)) \/ (~ (x0 = x1)).
Definition term51 (x0 : nat) := ~ ((NUMERAL x0) = x0).
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((Nat.mul x0 x1) = (Nat.mul x2 x3))).
Definition term18 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (((Nat.mul y1 y0) = x0) = ((Nat.mul (NUMERAL y1) (NUMERAL y0)) = (NUMERAL x0)))) -> ~ (forall y2 : nat, (NUMERAL y2) = y2).
Definition term101 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term82 (x0 : nat) (x1 : nat) := (~ (~ (x0 = x1))) -> (NUMERAL x0) = (NUMERAL x1).
Definition term85 (x0 : nat) (x1 : nat) := ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (Nat.mul x0 x1)) -> (NUMERAL (Nat.mul (NUMERAL x0) (NUMERAL x1))) = (NUMERAL (Nat.mul x0 x1)).
Definition term89 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term9 := ~ (forall y0 : nat, (NUMERAL y0) = y0).
Definition term16 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (((Nat.mul y0 x0) = x1) = ((Nat.mul (NUMERAL y0) (NUMERAL x0)) = (NUMERAL x1)))) -> ~ (forall y1 : nat, (NUMERAL y1) = y1).
Definition term68 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) := (((~ (((Nat.mul x0 x1) = x2) = ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL x2)))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ (((Nat.mul x0 x1) = x2) = ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL x2)))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> ((~ (((Nat.mul x0 x1) = x2) = ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL x2)))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ (((Nat.mul x0 x1) = x2) = ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL x2)))) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term54 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x3)) \/ ((Nat.mul x0 x1) = (Nat.mul x2 x3)).
Definition term44 (x0 : nat) (x1 : nat) := (~ (x0 = x1)) \/ ((NUMERAL x0) = (NUMERAL x1)).
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ~ ((Nat.mul (NUMERAL x0) (NUMERAL x1)) = (NUMERAL y0))) x2.
Definition term17 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (((Nat.mul y1 y0) = x0) = ((Nat.mul (NUMERAL y1) (NUMERAL y0)) = (NUMERAL x0)))) -> (forall y2 : nat, (NUMERAL y2) = y2) -> False.
Definition term102 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term88 (x0 : nat) (x1 : nat) := ~ ((NUMERAL (Nat.mul (NUMERAL x0) (NUMERAL x1))) = (NUMERAL (Nat.mul x0 x1))).
Definition term119 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (((Nat.mul y0 x0) = x1) = ((Nat.mul (NUMERAL y0) (NUMERAL x0)) = (NUMERAL x1)))) -> (forall y1 : nat, (NUMERAL y1) = y1) -> False) x2.
Definition term13 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (((Nat.mul y0 x0) = x1) = ((Nat.mul (NUMERAL y0) (NUMERAL x0)) = (NUMERAL x1)))) -> (forall y1 : nat, (NUMERAL y1) = y1) -> False.
Definition term22 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (((Nat.mul y2 y1) = y0) = ((Nat.mul (NUMERAL y2) (NUMERAL y1)) = (NUMERAL y0)))) -> ~ (forall y3 : nat, (NUMERAL y3) = y3).
Definition term21 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (((Nat.mul y2 y1) = y0) = ((Nat.mul (NUMERAL y2) (NUMERAL y1)) = (NUMERAL y0)))) -> (forall y3 : nat, (NUMERAL y3) = y3) -> False.
Definition term83 (x0 : nat) (x1 : nat) := imp (~ (~ (x0 = x1))).
Definition term112 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((NUMERAL x0) = (Nat.mul x1 x2)).
