Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term59 (x0 : nat) := BIT0 (BIT0 x0).
Definition term56 (x0 : nat) (x1 : nat) := Nat.pow (BIT0 x0) x1.
Definition term58 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow (BIT0 x0) x1).
Definition term49 := fun y0 : nat => (NUMERAL (BIT0 (BIT1 0))) = y0.
Definition term11 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y1) = (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (y1 = y2))) x0.
Definition term25 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term32 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term0 := ((0 = 0) = True) /\ ((forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))))).
Definition term1 := (forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))))).
Definition term73 (x0 : nat) := Nat.pow (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term87 := or ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)).
Definition term61 (x0 : nat) (x1 : nat) := Nat.pow (Nat.add x0 x0) x1.
Definition term33 (x0 : nat) (x1 : nat) := @eq nat (Nat.mul x0 (Nat.mul x1 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL (BIT0 (BIT1 0)))))).
Definition term46 (x0 : nat) := (fun y0 : nat => (Nat.add y0 y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) x0.
Definition term63 (x0 : nat) := Nat.add (BIT0 x0) (BIT0 x0).
Definition term64 (x0 : nat) := Nat.add (BIT0 x0).
Definition term9 (x0 : nat) := forall y0 : nat, ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0).
Definition term81 (x0 : nat) := @eq nat (Nat.mul (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0)).
Definition term66 (x0 : nat) := Nat.add (Nat.add x0 x0) (Nat.add x0 x0).
Definition term83 (x0 : nat) := @eq nat (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.mul x0 x0))).
Definition term80 (x0 : nat) := Nat.mul (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term48 := exists y0 : nat, (NUMERAL (BIT0 (BIT1 0))) = y0.
Definition term70 (x0 : nat) := Nat.pow (Nat.add x0 x0) (NUMERAL (BIT0 (BIT1 0))).
Definition term4 (x0 : nat) := (fun y0 : nat => ((BIT1 y0) = 0) = False) x0.
Definition term6 (x0 : nat) := (fun y0 : nat => ((BIT0 y0) = 0) = (y0 = 0)) x0.
Definition term78 (x0 : nat) := @eq nat (Nat.mul x0 x0).
Definition term75 (x0 : nat) := @eq nat (Nat.pow (Nat.add x0 x0) (NUMERAL (BIT0 (BIT1 0)))).
Definition term31 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.mul x1 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL (BIT0 (BIT1 0))))).
Definition term77 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.add x0 x0).
Definition term55 (x0 : nat) := Nat.pow (BIT0 x0) (NUMERAL (BIT0 (BIT1 0))).
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (x1 = x2).
Definition term39 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.mul x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term13 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.mul x0 y0) = (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (y0 = y1))) x1.
Definition term28 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term34 (x0 : nat) (x1 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.mul x0 x1).
Definition term42 := fun y0 : nat => (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0).
Definition term27 := Nat.mul (NUMERAL (BIT0 (BIT1 0))).
Definition term24 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term3 := forall y0 : nat, ((BIT1 y0) = 0) = False.
Definition term47 (x0 : nat) := (fun y0 : nat => (BIT0 y0) = (Nat.add y0 y0)) x0.
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.pow x0 y0) = x1) = ((Nat.pow (Nat.add x0 x0) y0) = (Nat.add (Nat.add x1 x1) (Nat.add x1 x1)))) x2.
Definition term44 := forall y0 : nat, (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0) = (Nat.add y0 y0).
Definition term30 (x0 : nat) := Nat.mul x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL (BIT0 (BIT1 0)))).
Definition term67 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Nat.pow x0 y0) = x1) = ((Nat.pow (Nat.add x0 x0) y0) = (Nat.add (Nat.add x1 x1) (Nat.add x1 x1))).
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.mul x0 x1) x2.
Definition term5 := forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0).
Definition term12 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.mul x0 y0) = (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (y0 = y1)).
Definition term7 := forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1).
Definition term88 (x0 : nat) (x1 : nat) := ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ ((Nat.mul x0 x0) = x1).
Definition term74 (x0 : nat) := Nat.pow (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (NUMERAL (BIT0 (BIT1 0))).
Definition term76 (x0 : nat) := @eq nat (Nat.pow (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (NUMERAL (BIT0 (BIT1 0)))).
Definition term45 := forall y0 : nat, (Nat.add y0 y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term14 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.mul x0 x1) = (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (x1 = y0)).
Definition term41 (x0 : nat) := Nat.pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term37 (x0 : nat) (x1 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.mul x0 x1)).
Definition term52 (x0 : nat) (x1 : nat) := @eq Prop ((Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1).
Definition term51 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow x0 x1).
Definition term82 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.mul x0 x0)).
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (((Nat.pow x0 x1) = x2) = ((Nat.pow (Nat.add x0 x0) x1) = (Nat.add (Nat.add x2 x2) (Nat.add x2 x2)))).
Definition term23 := NUMERAL (BIT0 (BIT1 0)).
Definition term84 (x0 : nat) (x1 : nat) := ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)) \/ ((Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.mul x0 x0)) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term54 (x0 : nat) := Nat.pow (BIT0 x0).
Definition term21 (x0 : nat) (x1 : nat) := Nat.mul (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term62 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow (Nat.add x0 x0) x1).
Definition term29 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.mul x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term50 (x0 : nat) := @eq nat (Nat.pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term43 := fun y0 : nat => (Nat.add y0 y0) = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term38 (x0 : nat) (x1 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.mul x0 (Nat.mul x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term8 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1)) x0.
Definition term35 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1).
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.mul x1 x2).
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.mul x0 x1) = (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (x1 = y0))) x2.
Definition term36 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.mul x1 (NUMERAL (BIT0 (BIT1 0)))).
Definition term86 := BIT0 (BIT1 0).
Definition term22 (x0 : nat) (x1 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.mul x0 (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x1)).
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Nat.pow x0 x1) = x2).
Definition term40 (x0 : nat) := (fun y0 : nat => (Nat.pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (Nat.mul y0 y0)) x0.
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.mul (Nat.mul x1 x0) x2) = (Nat.mul x1 (Nat.mul x0 x2))) /\ ((Nat.mul x1 (Nat.mul x0 x2)) = (Nat.mul x0 (Nat.mul x1 x2))).
Definition term65 (x0 : nat) := Nat.add (Nat.add x0 x0).
Definition term60 (x0 : nat) := Nat.pow (Nat.add x0 x0).
Definition term57 (x0 : nat) := @eq nat (Nat.pow (BIT0 x0) (NUMERAL (BIT0 (BIT1 0)))).
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : nat => ((Nat.pow x0 y0) = x1) = ((Nat.pow (Nat.add x0 x0) y0) = (Nat.add (Nat.add x1 x1) (Nat.add x1 x1)))) x2).
Definition term89 (x0 : nat) (x1 : nat) := False \/ ((Nat.mul x0 x0) = x1).
Definition term79 (x0 : nat) (x1 : nat) := @eq Prop ((Nat.mul x0 x0) = x1).
Definition term2 := (forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))).
Definition term17 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (y0 = y0) = True) x0.
Definition term10 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0)) x1.
Definition term69 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.pow x0 y0) = x1) = ((Nat.pow (Nat.add x0 x0) y0) = (Nat.add (Nat.add x1 x1) (Nat.add x1 x1)))) (NUMERAL (BIT0 (BIT1 0))).
Definition term85 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (Nat.mul x0 x0).
Definition term26 (x0 : nat) := Nat.mul x0 (NUMERAL (BIT0 (BIT1 0))).