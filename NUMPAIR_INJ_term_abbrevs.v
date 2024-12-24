Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((fun y0 : nat => (NUMPAIR y0 x0) = (NUMPAIR x1 x2)) x3).
Definition term45 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((fun y0 : nat => (y0 = x0) /\ (x1 = x2)) x3).
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((NUMPAIR x1 x0) = (NUMPAIR x2 y0)) -> x1 = x2.
Definition term40 (x0 : nat) (x1 : nat) := @eq nat (NUMPAIR x0 x1).
Definition term19 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.add x0 y0) = (Nat.add x1 y0)) = (x0 = x1).
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = x1) /\ (x2 = x3).
Definition term31 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((NUMPAIR y0 y1) = (NUMPAIR y2 y3)) -> y0 = y2) x0.
Definition term21 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y1) = (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (y1 = y2))) x0.
Definition term16 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y2) = (Nat.add y1 y2)) = (y0 = y1)) x0.
Definition term1 := ((0 = 0) = True) /\ ((forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))))).
Definition term0 := (forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1)) /\ (((0 = 0) = True) /\ ((forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))))))).
Definition term60 (x0 : nat) := Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term75 (x0 : nat) (x1 : nat) := (x0 = x1) -> x0 = x1.
Definition term2 := (forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))))).
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.add x0 y0) = (Nat.add x1 y0)) = (x0 = x1)) x2.
Definition term72 := or ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)).
Definition term57 (x0 : nat) (x1 : nat) (x2 : nat) := ((NUMPAIR x0 x1) = (NUMPAIR x0 x2)) -> (x0 = x0) /\ (x1 = x2).
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((NUMPAIR x0 x1) = (NUMPAIR x2 x3)).
Definition term10 (x0 : nat) := forall y0 : nat, ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0).
Definition term55 (x0 : nat) := and (x0 = x0).
Definition term59 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0) = (NUMERAL 0)) \/ ((Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1) (NUMERAL (BIT1 0))) = (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x2) (NUMERAL (BIT1 0)))).
Definition term49 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (NUMPAIR y0 x0) = (NUMPAIR x2 x1)) x2.
Definition term77 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((NUMPAIR x0 x2) = (NUMPAIR x1 x3)) -> (x0 = x1) /\ (x2 = x3).
Definition term5 (x0 : nat) := (fun y0 : nat => ((BIT1 y0) = 0) = False) x0.
Definition term7 (x0 : nat) := (fun y0 : nat => ((BIT0 y0) = 0) = (y0 = 0)) x0.
Definition term65 := and ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)).
Definition term78 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (((NUMPAIR x0 x1) = (NUMPAIR x2 x3)) -> (x0 = x2) /\ (x1 = x3)) /\ (((x0 = x2) /\ (x1 = x3)) -> (NUMPAIR x0 x1) = (NUMPAIR x2 x3)).
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (x1 = x2).
Definition term23 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.mul x0 y0) = (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (y0 = y1))) x1.
Definition term18 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add x0 y1) = (Nat.add y0 y1)) = (x0 = y0)) x1.
Definition term66 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term56 (x0 : nat) (x1 : nat) := True /\ (x0 = x1).
Definition term28 (x0 : nat) := forall y0 : nat, (NUMPAIR x0 y0) = (Nat.mul (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (NUMERAL (BIT1 0)))).
Definition term69 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term15 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0))).
Definition term4 := forall y0 : nat, ((BIT1 y0) = 0) = False.
Definition term74 (x0 : nat) (x1 : nat) := imp (x0 = x1).
Definition term73 (x0 : nat) (x1 : nat) := False \/ (x0 = x1).
Definition term41 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (y0 = x0) /\ (x1 = x2).
Definition term43 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (y0 = x2) /\ (x0 = x1)) x2.
Definition term6 := forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0).
Definition term82 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((NUMPAIR y0 y1) = (NUMPAIR y2 y3)) = ((y0 = y2) /\ (y1 = y3)).
Definition term81 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((NUMPAIR x0 y0) = (NUMPAIR y1 y2)) = ((x0 = y1) /\ (y0 = y2)).
Definition term80 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((NUMPAIR x0 x1) = (NUMPAIR y0 y1)) = ((x0 = y0) /\ (x1 = y1)).
Definition term34 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((NUMPAIR x1 x0) = (NUMPAIR y0 y1)) -> x1 = y0.
Definition term32 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((NUMPAIR x0 y0) = (NUMPAIR y1 y2)) -> x0 = y1.
Definition term22 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.mul x0 y0) = (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (y0 = y1)).
Definition term17 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.add x0 y1) = (Nat.add y0 y1)) = (x0 = y0).
Definition term8 := forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1).
Definition term14 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.pow x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) x1.
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((NUMPAIR x1 x0) = (NUMPAIR y0 y1)) -> x1 = y0) x2.
Definition term33 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((NUMPAIR x0 y0) = (NUMPAIR y1 y2)) -> x0 = y1) x1.
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((NUMPAIR x2 x0) = (NUMPAIR x3 x1)) -> x2 = x3.
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((NUMPAIR x1 x0) = (NUMPAIR x2 y0)) -> x1 = x2) x3.
Definition term79 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((NUMPAIR x0 x2) = (NUMPAIR x1 y0)) = ((x0 = x1) /\ (x2 = y0)).
Definition term24 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.mul x0 x1) = (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (x1 = y0)).
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x0 = x2) /\ (x1 = x3)) -> (NUMPAIR x0 x1) = (NUMPAIR x2 x3).
Definition term52 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1) (NUMERAL (BIT1 0)))).
Definition term54 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Nat.mul (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x1) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (NUMERAL (BIT1 0)))) = (Nat.mul (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x1) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x2) (NUMERAL (BIT1 0))))).
Definition term29 (x0 : nat) (x1 : nat) := (fun y0 : nat => (NUMPAIR x0 y0) = (Nat.mul (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) (NUMERAL (BIT1 0))))) x1.
Definition term63 := NUMERAL (BIT0 (BIT1 0)).
Definition term27 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (NUMPAIR y0 y1) = (Nat.mul (Nat.pow (NUMERAL (BIT0 (BIT1 0))) y0) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1) (NUMERAL (BIT1 0))))) x0.
Definition term12 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) x0.
Definition term9 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1)) x0.
Definition term58 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.mul (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1) (NUMERAL (BIT1 0)))) = (Nat.mul (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x2) (NUMERAL (BIT1 0))))) -> x1 = x2.
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.mul x0 x1) = (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (x1 = y0))) x2.
Definition term64 := BIT0 (BIT1 0).
Definition term68 (x0 : nat) := or ((Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0) = (NUMERAL 0)).
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => (NUMPAIR y0 x0) = (NUMPAIR x1 x2)) x3.
Definition term61 (x0 : nat) := Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (NUMERAL (BIT1 0)).
Definition term3 := (forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))).
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((NUMPAIR x1 x0) = (NUMPAIR x1 x2)).
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => (y0 = x0) /\ (x1 = x2)) x3.
Definition term44 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x0) /\ (x1 = x2).
Definition term47 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (NUMPAIR y0 x0) = (NUMPAIR x1 x2).
Definition term11 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0)) x1.
Definition term30 (x0 : nat) (x1 : nat) := Nat.mul (Nat.pow (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.add (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1) (NUMERAL (BIT1 0))).
Definition term46 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((x0 = x1) /\ (x2 = x3)).
Definition term67 (x0 : nat) := False /\ (~ (x0 = (NUMERAL 0))).
Definition term62 (x0 : nat) := ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) /\ (~ (x0 = (NUMERAL 0))).
Definition term70 := NUMERAL (BIT1 0).
Definition term71 (x0 : nat) (x1 : nat) := ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ (x0 = x1).
Definition term13 (x0 : nat) := forall y0 : nat, ((Nat.pow x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0)))).
