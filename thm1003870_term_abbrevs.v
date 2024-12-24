Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term47 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term73 := (~ False) -> False.
Definition term23 (x0 : nat) (x1 : nat) := ((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) /\ (~ ((Nat.mul x0 x0) = x1)).
Definition term55 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term71 (x0 : nat) := (~ ((Nat.mul x0 x0) = (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))))) -> (Nat.mul x0 x0) = (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term37 (x0 : nat) := ~ ((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul x0 x0)).
Definition term61 (x0 : Prop) := ~ (~ x0).
Definition term31 (x0 : nat) := ~ ((Nat.mul x0 x0) = (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term24 (x0 : nat) (x1 : nat) := (~ ((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1)) /\ ((Nat.mul x0 x0) = x1).
Definition term72 (x0 : nat) := ((Nat.mul x0 x0) = (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0))))) -> False.
Definition term4 (x0 : nat) (x1 : nat) := (~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul x0 x0) = x1))) -> (forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) -> False.
Definition term60 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term6 (x0 : nat) (x1 : nat) := (((~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul x0 x0) = x1))) -> (forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) -> False) -> (~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul x0 x0) = x1))) -> (forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) -> False) -> (~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul x0 x0) = x1))) -> (forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) -> False.
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term66 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term10 := forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0).
Definition term54 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term64 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term9 := ~ (forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)).
Definition term33 (x0 : nat) (x1 : nat) := @eq Prop (~ ((Nat.mul x0 x0) = x1)).
Definition term22 (x0 : nat) (x1 : nat) := (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) /\ (~ ((Nat.mul x0 x0) = x1))) \/ ((~ ((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1)) /\ ((Nat.mul x0 x0) = x1)).
Definition term42 (x0 : Prop) := (~ x0) -> x0.
Definition term65 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = x0) /\ (x1 = x2).
Definition term56 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term58 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term50 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term3 (x0 : nat) (x1 : nat) := ~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul x0 x0) = x1)).
Definition term14 (x0 : nat) := fun y0 : nat => (~ (((Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0) = ((Nat.mul y0 y0) = x0))) -> ~ (forall y1 : nat, (Nat.pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y1 y1)).
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term36 (x0 : nat) := (fun y0 : nat => ~ ((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = y0)) (Nat.mul x0 x0).
Definition term57 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term21 := fun y0 : nat => (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0).
Definition term20 := forall y0 : nat, forall y1 : nat, (~ (((Nat.pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0) = ((Nat.mul y1 y1) = y0))) -> ~ (forall y2 : nat, (Nat.pow y2 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y2 y2)).
Definition term19 := forall y0 : nat, forall y1 : nat, (~ (((Nat.pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0) = ((Nat.mul y1 y1) = y0))) -> (forall y2 : nat, (Nat.pow y2 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y2 y2)) -> False.
Definition term34 (x0 : nat) := fun y0 : nat => ~ ((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = y0).
Definition term44 (x0 : nat) := ~ ((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term12 (x0 : nat) (x1 : nat) := (~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul x0 x0) = x1))) -> ~ (forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)).
Definition term8 := (forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) -> False.
Definition term46 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term43 (x0 : nat) := (~ ((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))))) -> (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term1 (x0 : nat) := Nat.pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term76 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (((Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0) = ((Nat.mul y0 y0) = x0))) -> (forall y1 : nat, (Nat.pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y1 y1)) -> False) x1.
Definition term11 (x0 : nat) (x1 : nat) := imp (~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul x0 x0) = x1))).
Definition term49 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term15 (x0 : nat) := forall y0 : nat, (~ (((Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0) = ((Nat.mul y0 y0) = x0))) -> (forall y1 : nat, (Nat.pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y1 y1)) -> False.
Definition term63 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term74 (x0 : nat) := ((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul x0 x0)) -> False.
Definition term38 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => ~ ((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = y0)) x1).
Definition term32 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => ~ ((Nat.mul x0 x0) = y0)) x1).
Definition term75 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (((Nat.pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0) = ((Nat.mul y1 y1) = y0))) -> (forall y2 : nat, (Nat.pow y2 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y2 y2)) -> False) x0.
Definition term5 (x0 : nat) (x1 : nat) := ((~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul x0 x0) = x1))) -> (forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) -> False) -> (~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul x0 x0) = x1))) -> (forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) -> False.
Definition term59 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term70 (x0 : nat) := (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul x0 x0)) /\ ((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))))) -> (Nat.mul x0 x0) = (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term30 (x0 : nat) := (fun y0 : nat => ~ ((Nat.mul x0 x0) = y0)) (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term25 (x0 : nat) := (fun y0 : nat => (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) x0.
Definition term28 (x0 : nat) := fun y0 : nat => ~ ((Nat.mul x0 x0) = y0).
Definition term41 (x0 : nat) := (~ ((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul x0 x0))) -> (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul x0 x0).
Definition term18 := fun y0 : nat => forall y1 : nat, (~ (((Nat.pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0) = ((Nat.mul y1 y1) = y0))) -> ~ (forall y2 : nat, (Nat.pow y2 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y2 y2)).
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term35 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ ((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = y0)) x1.
Definition term29 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ ((Nat.mul x0 x0) = y0)) x1.
Definition term2 (x0 : nat) (x1 : nat) := (~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul x0 x0) = x1))) -> False.
Definition term45 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term16 (x0 : nat) := forall y0 : nat, (~ (((Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0) = ((Nat.mul y0 y0) = x0))) -> ~ (forall y1 : nat, (Nat.pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y1 y1)).
Definition term39 (x0 : nat) (x1 : nat) := @eq Prop (~ ((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1)).
Definition term62 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term7 (x0 : nat) (x1 : nat) := (((~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul x0 x0) = x1))) -> (forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) -> False) -> (~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul x0 x0) = x1))) -> (forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) -> False) -> ((~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul x0 x0) = x1))) -> (forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) -> False) -> (~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul x0 x0) = x1))) -> (forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) -> False.
Definition term48 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term26 (x0 : nat) (x1 : nat) := ~ ((Nat.mul x0 x0) = x1).
Definition term17 := fun y0 : nat => forall y1 : nat, (~ (((Nat.pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0) = ((Nat.mul y1 y1) = y0))) -> (forall y2 : nat, (Nat.pow y2 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y2 y2)) -> False.
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term13 (x0 : nat) := fun y0 : nat => (~ (((Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0) = ((Nat.mul y0 y0) = x0))) -> (forall y1 : nat, (Nat.pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y1 y1)) -> False.
Definition term69 (x0 : nat) := ((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul x0 x0)) /\ ((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term27 (x0 : nat) (x1 : nat) := ~ ((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1).
