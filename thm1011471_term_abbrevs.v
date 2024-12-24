Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term63 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term94 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp (~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3))))).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (NUMERAL x0) (NUMERAL y0)) = True) x1.
Definition term16 (x0 : nat) (x1 : nat) := (((~ (Peano.le x1 (Nat.add x0 x1))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> False) -> (~ (Peano.le x1 (Nat.add x0 x1))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> False) -> (~ (Peano.le x1 (Nat.add x0 x1))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> False.
Definition term62 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) \/ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3))).
Definition term102 := (~ False) -> False.
Definition term24 (x0 : nat) (x1 : nat) := imp (~ (Peano.le x1 (Nat.add x0 x1))).
Definition term38 (x0 : nat) := fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term85 (x0 : Prop) := ~ (~ x0).
Definition term57 (x0 : nat) (x1 : nat) := (~ ((Nat.add x1 x0) = (Nat.add x0 x1))) -> (Nat.add x1 x0) = (Nat.add x0 x1).
Definition term35 (x0 : nat) := fun y0 : nat => Peano.le x0 (Nat.add x0 y0).
Definition term5 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => (Peano.le (NUMERAL x0) (NUMERAL y0)) = True) x1).
Definition term90 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x2 = x0))) /\ (~ (~ (Peano.le x1 x2))).
Definition term55 (x0 : nat) := ~ (x0 = x0).
Definition term11 (x0 : Prop) := (~ x0) -> False.
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x3) \/ ((~ (x1 = x0)) \/ ((~ (Peano.le x1 x2)) \/ (~ (x2 = x3)))).
Definition term66 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x1)) \/ (~ (x1 = x2)).
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x3) \/ ((~ (Peano.le x1 x2)) \/ (~ (x2 = x3))).
Definition term8 (x0 : nat) := Peano.le (NUMERAL x0).
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x0)) \/ ((Peano.le x0 x3) \/ ((~ (Peano.le x1 x2)) \/ (~ (x2 = x3)))).
Definition term28 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 (Nat.add y0 x0))) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> (forall y1 : nat, forall y2 : nat, Peano.le y1 (Nat.add y1 y2)) -> False.
Definition term79 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term88 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term19 := ~ (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)).
Definition term80 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ (~ (Peano.le x0 x1))))) -> Peano.le x2 x3.
Definition term56 (x0 : Prop) := (~ x0) -> x0.
Definition term82 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term36 (x0 : nat) := forall y0 : nat, Peano.le x0 (Nat.add x0 y0).
Definition term54 (x0 : nat) := (~ (x0 = x0)) -> x0 = x0.
Definition term22 := (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> False.
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (NUMERAL x1) (NUMERAL y0)) = True) (Nat.add x0 x1).
Definition term61 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((Peano.le x1 x3) \/ ((~ (Peano.le x0 x2)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))))).
Definition term4 (x0 : nat) (x1 : nat) := Peano.le (NUMERAL x1) (NUMERAL (Nat.add x0 x1)).
Definition term78 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3)))).
Definition term40 := fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0).
Definition term95 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((x2 = x0) /\ ((x3 = x1) /\ (Peano.le x2 x3))).
Definition term1 (x0 : nat) := fun y0 : nat => (Peano.le (NUMERAL x0) (NUMERAL y0)) = True.
Definition term45 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le x0 (Nat.add x0 y0)) x1.
Definition term59 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 (Nat.add x0 x1))) -> Peano.le x0 (Nat.add x0 x1).
Definition term7 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.le (NUMERAL x0) (NUMERAL x1)) = True).
Definition term29 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 (Nat.add y0 x0))) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> ~ (forall y1 : nat, forall y2 : nat, Peano.le y1 (Nat.add y1 y2)).
Definition term64 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term67 (x0 : nat) (x1 : nat) := or (Peano.le x0 x1).
Definition term98 (x0 : nat) (x1 : nat) := (x0 = x0) /\ (((Nat.add x0 x1) = (Nat.add x1 x0)) /\ (Peano.le x0 (Nat.add x0 x1))).
Definition term101 (x0 : nat) (x1 : nat) := (Peano.le x1 (Nat.add x0 x1)) -> False.
Definition term18 := (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> False.
Definition term92 (x0 : nat) (x1 : nat) (x2 : nat) := (x2 = x0) /\ (Peano.le x1 x2).
Definition term12 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 (Nat.add x0 x1))) -> False.
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3))).
Definition term0 (x0 : nat) := (fun y0 : nat => (NUMERAL y0) = y0) x0.
Definition term47 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le x2 x3) = (Peano.le x0 x1)) -> (Peano.le x0 x1) \/ (~ (Peano.le x2 x3)).
Definition term81 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term41 := forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0).
Definition term33 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 (Nat.add y1 y0))) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> ~ (forall y2 : nat, forall y3 : nat, Peano.le y2 (Nat.add y2 y3)).
Definition term32 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 (Nat.add y1 y0))) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> (forall y2 : nat, forall y3 : nat, Peano.le y2 (Nat.add y2 y3)) -> False.
Definition term20 := forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1).
Definition term15 (x0 : nat) (x1 : nat) := ((~ (Peano.le x1 (Nat.add x0 x1))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> False) -> (~ (Peano.le x1 (Nat.add x0 x1))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> False.
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x2 = x0) -> (~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3))).
Definition term83 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3)))).
Definition term65 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x2 = x0)) \/ (~ (Peano.le x1 x2)).
Definition term26 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 (Nat.add y0 x0))) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> (forall y1 : nat, forall y2 : nat, Peano.le y1 (Nat.add y1 y2)) -> False.
Definition term49 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x3 = x1) -> (Peano.le x0 x1) \/ (~ (Peano.le x2 x3)).
Definition term105 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add x0 x1) = x2) -> (Peano.le (NUMERAL x1) (NUMERAL x2)) = True.
Definition term39 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term17 (x0 : nat) (x1 : nat) := (((~ (Peano.le x1 (Nat.add x0 x1))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> False) -> (~ (Peano.le x1 (Nat.add x0 x1))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> False) -> ((~ (Peano.le x1 (Nat.add x0 x1))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> False) -> (~ (Peano.le x1 (Nat.add x0 x1))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> False.
Definition term43 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0)) x1.
Definition term87 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) \/ (~ (Peano.le x2 x3)).
Definition term46 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term96 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x0 = x2) /\ ((x1 = x3) /\ (Peano.le x0 x1))) -> Peano.le x2 x3.
Definition term104 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le x0 (Nat.add y0 x0))) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> (forall y1 : nat, forall y2 : nat, Peano.le y1 (Nat.add y1 y2)) -> False) x1.
Definition term99 (x0 : nat) (x1 : nat) := ((x1 = x1) /\ (((Nat.add x1 x0) = (Nat.add x0 x1)) /\ (Peano.le x1 (Nat.add x1 x0)))) -> Peano.le x1 (Nat.add x0 x1).
Definition term10 (x0 : nat) (x1 : nat) := Peano.le x1 (Nat.add x0 x1).
Definition term34 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.add x0 x1).
Definition term103 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 (Nat.add y1 y0))) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> (forall y2 : nat, forall y3 : nat, Peano.le y2 (Nat.add y2 y3)) -> False) x0.
Definition term44 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) x0.
Definition term42 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) x0.
Definition term93 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x2 = x0) /\ ((x3 = x1) /\ (Peano.le x2 x3)).
Definition term91 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term25 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 (Nat.add x0 x1))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> ~ (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)).
Definition term77 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3))).
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x0)) \/ ((~ (Peano.le x1 x2)) \/ (~ (x2 = x3))).
Definition term89 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x2 = x0)) \/ (~ (Peano.le x1 x2))).
Definition term6 (x0 : nat) (x1 : nat) := Peano.le (NUMERAL x0) (NUMERAL x1).
Definition term75 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3))))).
Definition term23 := (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> ~ (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)).
Definition term50 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term84 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (~ (x2 = x0))) /\ (~ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3)))).
Definition term58 (x0 : nat) (x1 : nat) := ~ ((Nat.add x1 x0) = (Nat.add x0 x1)).
Definition term13 (x0 : nat) (x1 : nat) := ~ (Peano.le x1 (Nat.add x0 x1)).
Definition term73 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.le x0 x2)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x1 x3) \/ ((~ (Peano.le x0 x2)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term97 (x0 : nat) (x1 : nat) := ((Nat.add x0 x1) = (Nat.add x1 x0)) /\ (Peano.le x0 (Nat.add x0 x1)).
Definition term100 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 (Nat.add x0 x1))) -> Peano.le x1 (Nat.add x0 x1).
Definition term86 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term69 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term60 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 (Nat.add x0 x1)).
Definition term9 (x0 : nat) (x1 : nat) := NUMERAL (Nat.add x0 x1).
Definition term37 := fun y0 : nat => forall y1 : nat, Peano.le y0 (Nat.add y0 y1).
Definition term21 := imp (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)).
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3)))).
Definition term14 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 (Nat.add x0 x1))) -> (forall y0 : nat, forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) -> (forall y0 : nat, forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) -> False.
Definition term27 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 (Nat.add y0 x0))) -> (forall y1 : nat, forall y2 : nat, (Nat.add y1 y2) = (Nat.add y2 y1)) -> ~ (forall y1 : nat, forall y2 : nat, Peano.le y1 (Nat.add y1 y2)).
Definition term31 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 (Nat.add y1 y0))) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> ~ (forall y2 : nat, forall y3 : nat, Peano.le y2 (Nat.add y2 y3)).
Definition term30 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 (Nat.add y1 y0))) -> (forall y2 : nat, forall y3 : nat, (Nat.add y2 y3) = (Nat.add y3 y2)) -> (forall y2 : nat, forall y3 : nat, Peano.le y2 (Nat.add y2 y3)) -> False.
