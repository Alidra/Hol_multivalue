Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term62 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term7 (x0 : nat) (x1 : nat) := (((~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL x1)))) -> (forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL x1)))) -> (forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL x1)))) -> (forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term85 (x0 : nat) := (((NUMERAL x0) = x0) /\ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL (BIT0 (BIT1 0))))) -> (Nat.pow (NUMERAL x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term120 := (~ False) -> False.
Definition term94 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term4 (x0 : nat) (x1 : nat) := ~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL x1))).
Definition term80 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = x1) /\ (x2 = x3).
Definition term76 (x0 : Prop) := ~ (~ x0).
Definition term41 (x0 : nat) (x1 : nat) := (x0 = x1) -> (NUMERAL x0) = (NUMERAL x1).
Definition term15 (x0 : nat) (x1 : nat) := imp (~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL x1)))).
Definition term75 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (~ (x0 = x1))) /\ (~ (~ (x2 = x3))).
Definition term97 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term112 (x0 : nat) := ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0))))) -> (NUMERAL (Nat.mul (NUMERAL x0) (NUMERAL x0))) = (NUMERAL (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop (((Nat.pow x0 x2) = (Nat.pow x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term9 := (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term13 := (forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term99 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term81 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp (~ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term3 (x0 : nat) (x1 : nat) := (~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL x1)))) -> False.
Definition term118 (x0 : nat) := (~ ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0))))))) -> (Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term27 := forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0).
Definition term2 (x0 : nat) := Nat.mul (NUMERAL x0) (NUMERAL x0).
Definition term19 (x0 : nat) := forall y0 : nat, (~ (((Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0) = ((Nat.mul (NUMERAL y0) (NUMERAL y0)) = (NUMERAL x0)))) -> (forall y1 : nat, (Nat.pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y1 y1)) -> (forall y1 : nat, (NUMERAL y1) = y1) -> False.
Definition term69 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term35 (x0 : nat) := fun y0 : nat => ~ ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL y0)).
Definition term79 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term50 (x0 : nat) := (~ ((NUMERAL (Nat.mul (NUMERAL x0) (NUMERAL x0))) = (Nat.mul (NUMERAL x0) (NUMERAL x0)))) -> (NUMERAL (Nat.mul (NUMERAL x0) (NUMERAL x0))) = (Nat.mul (NUMERAL x0) (NUMERAL x0)).
Definition term28 (x0 : nat) (x1 : nat) := (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) /\ (~ ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL x1)))) \/ ((~ ((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1)) /\ ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL x1))).
Definition term38 (x0 : nat) := ~ ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term117 (x0 : nat) := (((NUMERAL (Nat.mul (NUMERAL x0) (NUMERAL x0))) = (Nat.mul (NUMERAL x0) (NUMERAL x0))) /\ ((NUMERAL (Nat.mul (NUMERAL x0) (NUMERAL x0))) = (NUMERAL (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0))))))) -> (Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term52 (x0 : Prop) := (~ x0) -> x0.
Definition term98 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = x0) /\ (x1 = x2).
Definition term82 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((x0 = x1) /\ (x2 = x3)).
Definition term18 (x0 : nat) := fun y0 : nat => (~ (((Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0) = ((Nat.mul (NUMERAL y0) (NUMERAL y0)) = (NUMERAL x0)))) -> (forall y1 : nat, (Nat.pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y1 y1)) -> ~ (forall y1 : nat, (NUMERAL y1) = y1).
Definition term95 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term56 (x0 : nat) := (~ ((NUMERAL x0) = x0)) -> (NUMERAL x0) = x0.
Definition term73 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term53 (x0 : nat) := Nat.pow (NUMERAL x0) (NUMERAL (BIT0 (BIT1 0))).
Definition term92 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term119 (x0 : nat) := ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))))) -> False.
Definition term93 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term65 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term104 (x0 : nat) := (~ ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))))) -> (Nat.mul (NUMERAL x0) (NUMERAL x0)) = (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term66 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.pow x0 x2) = (Nat.pow x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term108 (x0 : nat) (x1 : nat) := @eq Prop (((NUMERAL x0) = (NUMERAL x1)) \/ (~ (x0 = x1))).
Definition term29 (x0 : nat) (x1 : nat) := ((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) /\ (~ ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL x1))).
Definition term86 (x0 : nat) := (~ ((Nat.pow (NUMERAL x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))))) -> (Nat.pow (NUMERAL x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term40 (x0 : nat) (x1 : nat) := @eq Prop (~ ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL x1))).
Definition term61 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.pow x0 x2) = (Nat.pow x1 x3)) \/ (~ (x2 = x3)).
Definition term5 (x0 : nat) (x1 : nat) := (~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL x1)))) -> (forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term59 := (~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL (BIT0 (BIT1 0))))) -> (NUMERAL (BIT0 (BIT1 0))) = (NUMERAL (BIT0 (BIT1 0))).
Definition term45 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x3)) \/ ((Nat.pow x0 x1) = (Nat.pow x2 x3)).
Definition term20 (x0 : nat) := forall y0 : nat, (~ (((Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0) = ((Nat.mul (NUMERAL y0) (NUMERAL y0)) = (NUMERAL x0)))) -> (forall y1 : nat, (Nat.pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y1 y1)) -> ~ (forall y1 : nat, (NUMERAL y1) = y1).
Definition term36 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL y0))) x1.
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term17 (x0 : nat) := fun y0 : nat => (~ (((Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0) = ((Nat.mul (NUMERAL y0) (NUMERAL y0)) = (NUMERAL x0)))) -> (forall y1 : nat, (Nat.pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y1 y1)) -> (forall y1 : nat, (NUMERAL y1) = y1) -> False.
Definition term51 (x0 : nat) := ~ ((NUMERAL (Nat.mul (NUMERAL x0) (NUMERAL x0))) = (Nat.mul (NUMERAL x0) (NUMERAL x0))).
Definition term91 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term33 (x0 : nat) (x1 : nat) := ~ ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL x1)).
Definition term121 (x0 : nat) (x1 : nat) := (~ ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL x1))) -> (Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL x1).
Definition term83 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x0 = x2) /\ (x1 = x3)) -> (Nat.pow x0 x1) = (Nat.pow x2 x3).
Definition term55 (x0 : nat) := ~ ((Nat.pow (NUMERAL x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul (NUMERAL x0) (NUMERAL x0))).
Definition term12 := imp (forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)).
Definition term111 (x0 : nat) (x1 : nat) := imp (x0 = x1).
Definition term32 (x0 : nat) := (fun y0 : nat => (NUMERAL y0) = y0) x0.
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((~ (x0 = x2)) \/ (~ (x1 = x3)))) -> (Nat.pow x0 x1) = (Nat.pow x2 x3).
Definition term14 := (forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) -> ~ (forall y0 : nat, (NUMERAL y0) = y0).
Definition term72 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term26 := fun y0 : nat => (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0).
Definition term24 := forall y0 : nat, forall y1 : nat, (~ (((Nat.pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0) = ((Nat.mul (NUMERAL y1) (NUMERAL y1)) = (NUMERAL y0)))) -> (forall y2 : nat, (Nat.pow y2 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y2 y2)) -> ~ (forall y2 : nat, (NUMERAL y2) = y2).
Definition term23 := forall y0 : nat, forall y1 : nat, (~ (((Nat.pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0) = ((Nat.mul (NUMERAL y1) (NUMERAL y1)) = (NUMERAL y0)))) -> (forall y2 : nat, (Nat.pow y2 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y2 y2)) -> (forall y2 : nat, (NUMERAL y2) = y2) -> False.
Definition term128 (x0 : nat) (x1 : nat) := (~ ((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1)) -> (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1.
Definition term6 (x0 : nat) (x1 : nat) := ((~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL x1)))) -> (forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL x1)))) -> (forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((Nat.pow x0 x1) = (Nat.pow x2 x3)))).
Definition term114 (x0 : nat) := (~ ((NUMERAL (Nat.mul (NUMERAL x0) (NUMERAL x0))) = (NUMERAL (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0))))))) -> (NUMERAL (Nat.mul (NUMERAL x0) (NUMERAL x0))) = (NUMERAL (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term44 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x1 = x3) -> (Nat.pow x0 x1) = (Nat.pow x2 x3).
Definition term11 := forall y0 : nat, (NUMERAL y0) = y0.
Definition term89 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term1 (x0 : nat) := Nat.pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term30 (x0 : nat) (x1 : nat) := (~ ((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1)) /\ ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL x1)).
Definition term90 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term116 (x0 : nat) := ((NUMERAL (Nat.mul (NUMERAL x0) (NUMERAL x0))) = (Nat.mul (NUMERAL x0) (NUMERAL x0))) /\ ((NUMERAL (Nat.mul (NUMERAL x0) (NUMERAL x0))) = (NUMERAL (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term8 (x0 : nat) (x1 : nat) := (((~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL x1)))) -> (forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL x1)))) -> (forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> ((~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL x1)))) -> (forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False) -> (~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL x1)))) -> (forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) -> (forall y0 : nat, (NUMERAL y0) = y0) -> False.
Definition term78 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term58 := NUMERAL (BIT0 (BIT1 0)).
Definition term103 (x0 : nat) := (((Nat.pow (NUMERAL x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul (NUMERAL x0) (NUMERAL x0))) /\ ((Nat.pow (NUMERAL x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))))) -> (Nat.mul (NUMERAL x0) (NUMERAL x0)) = (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term107 (x0 : nat) (x1 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((NUMERAL x0) = (NUMERAL x1))).
Definition term125 (x0 : nat) (x1 : nat) := ~ ((NUMERAL x0) = (Nat.pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term131 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (((Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0) = ((Nat.mul (NUMERAL y0) (NUMERAL y0)) = (NUMERAL x0)))) -> (forall y1 : nat, (Nat.pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y1 y1)) -> (forall y1 : nat, (NUMERAL y1) = y1) -> False) x1.
Definition term39 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => ~ ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL y0))) x1).
Definition term37 (x0 : nat) := (fun y0 : nat => ~ ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL y0))) (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term64 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x1)) \/ (((Nat.pow x0 x2) = (Nat.pow x1 x3)) \/ (~ (x2 = x3))).
Definition term130 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (((Nat.pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0) = ((Nat.mul (NUMERAL y1) (NUMERAL y1)) = (NUMERAL y0)))) -> (forall y2 : nat, (Nat.pow y2 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y2 y2)) -> (forall y2 : nat, (NUMERAL y2) = y2) -> False) x0.
Definition term122 (x0 : nat) (x1 : nat) := ((Nat.mul (NUMERAL x1) (NUMERAL x1)) = (NUMERAL x0)) /\ ((Nat.mul (NUMERAL x1) (NUMERAL x1)) = (Nat.pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term105 (x0 : nat) := ~ ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term115 (x0 : nat) := ~ ((NUMERAL (Nat.mul (NUMERAL x0) (NUMERAL x0))) = (NUMERAL (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term96 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term46 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = x2) -> (~ (x1 = x3)) \/ ((Nat.pow x0 x1) = (Nat.pow x2 x3)).
Definition term31 (x0 : nat) := (fun y0 : nat => (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) x0.
Definition term42 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x1)) \/ (~ (x2 = x3)).
Definition term129 (x0 : nat) (x1 : nat) := ((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) -> False.
Definition term25 := fun y0 : nat => (NUMERAL y0) = y0.
Definition term60 := ~ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL (BIT0 (BIT1 0)))).
Definition term49 (x0 : nat) := NUMERAL (Nat.mul (NUMERAL x0) (NUMERAL x0)).
Definition term106 (x0 : nat) (x1 : nat) := ((NUMERAL x0) = (NUMERAL x1)) \/ (~ (x0 = x1)).
Definition term84 (x0 : nat) := ((NUMERAL x0) = x0) /\ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL (BIT0 (BIT1 0)))).
Definition term57 (x0 : nat) := ~ ((NUMERAL x0) = x0).
Definition term47 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((Nat.pow x0 x1) = (Nat.pow x2 x3))).
Definition term100 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term16 (x0 : nat) (x1 : nat) := (~ (((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1) = ((Nat.mul (NUMERAL x0) (NUMERAL x0)) = (NUMERAL x1)))) -> (forall y0 : nat, (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) -> ~ (forall y0 : nat, (NUMERAL y0) = y0).
Definition term54 (x0 : nat) := (~ ((Nat.pow (NUMERAL x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul (NUMERAL x0) (NUMERAL x0)))) -> (Nat.pow (NUMERAL x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul (NUMERAL x0) (NUMERAL x0)).
Definition term109 (x0 : nat) (x1 : nat) := (~ (~ (x0 = x1))) -> (NUMERAL x0) = (NUMERAL x1).
Definition term126 (x0 : nat) (x1 : nat) := ((NUMERAL x1) = (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0))))) /\ ((NUMERAL x1) = x1).
Definition term88 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term10 := ~ (forall y0 : nat, (NUMERAL y0) = y0).
Definition term77 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term87 (x0 : nat) := ~ ((Nat.pow (NUMERAL x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term63 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term43 (x0 : nat) (x1 : nat) := (~ (x0 = x1)) \/ ((NUMERAL x0) = (NUMERAL x1)).
Definition term102 (x0 : nat) := ((Nat.pow (NUMERAL x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul (NUMERAL x0) (NUMERAL x0))) /\ ((Nat.pow (NUMERAL x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term101 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term124 (x0 : nat) (x1 : nat) := (~ ((NUMERAL x0) = (Nat.pow x1 (NUMERAL (BIT0 (BIT1 0)))))) -> (NUMERAL x0) = (Nat.pow x1 (NUMERAL (BIT0 (BIT1 0)))).
Definition term123 (x0 : nat) (x1 : nat) := (((Nat.mul (NUMERAL x1) (NUMERAL x1)) = (NUMERAL x0)) /\ ((Nat.mul (NUMERAL x1) (NUMERAL x1)) = (Nat.pow x1 (NUMERAL (BIT0 (BIT1 0)))))) -> (NUMERAL x0) = (Nat.pow x1 (NUMERAL (BIT0 (BIT1 0)))).
Definition term22 := fun y0 : nat => forall y1 : nat, (~ (((Nat.pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0) = ((Nat.mul (NUMERAL y1) (NUMERAL y1)) = (NUMERAL y0)))) -> (forall y2 : nat, (Nat.pow y2 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y2 y2)) -> ~ (forall y2 : nat, (NUMERAL y2) = y2).
Definition term21 := fun y0 : nat => forall y1 : nat, (~ (((Nat.pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0) = ((Nat.mul (NUMERAL y1) (NUMERAL y1)) = (NUMERAL y0)))) -> (forall y2 : nat, (Nat.pow y2 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y2 y2)) -> (forall y2 : nat, (NUMERAL y2) = y2) -> False.
Definition term34 (x0 : nat) (x1 : nat) := ~ ((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1).
Definition term127 (x0 : nat) (x1 : nat) := (((NUMERAL x1) = (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0))))) /\ ((NUMERAL x1) = x1)) -> (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1.
Definition term113 (x0 : nat) := NUMERAL (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term110 (x0 : nat) (x1 : nat) := imp (~ (~ (x0 = x1))).
