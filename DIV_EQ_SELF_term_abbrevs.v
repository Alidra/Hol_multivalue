Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term35 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term51 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) \/ (x1 = (NUMERAL (BIT1 0))).
Definition term82 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.lt (Nat.mul x0 y0) (Nat.mul x1 y0)) = ((Peano.lt x0 x1) /\ (~ (y0 = (NUMERAL 0))))) x2.
Definition term42 (x0 : nat) := (x0 = (NUMERAL (BIT1 0))) \/ (~ (x0 = (NUMERAL (BIT1 0)))).
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (x1 = (NUMERAL 0))) -> (Peano.lt (Nat.div x0 x1) y0) = (Peano.lt x0 (Nat.mul x1 y0))) x2.
Definition term4 (x0 : nat) := fun y0 : nat => (Peano.lt y0 x0) = (~ (Peano.le x0 y0)).
Definition term6 (x0 : nat) := forall y0 : nat, (Peano.lt y0 x0) = (~ (Peano.le x0 y0)).
Definition term18 (x0 : nat) := (fun y0 : nat => (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) x0.
Definition term48 := @eq nat (NUMERAL 0).
Definition term23 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term78 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.lt (Nat.mul y0 y2) (Nat.mul y1 y2)) = ((Peano.lt y0 y1) /\ (~ (y2 = (NUMERAL 0))))) x0.
Definition term65 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.lt (Nat.div y1 y0) y2) = (Peano.lt y1 (Nat.mul y0 y2))) x0.
Definition term58 (x0 : nat) := (~ (x0 = (NUMERAL (BIT1 0)))) -> (x0 = (NUMERAL (BIT1 0))) = False.
Definition term3 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term43 (x0 : nat) := ~ (x0 = (NUMERAL (BIT1 0))).
Definition term87 (x0 : nat) := (Peano.lt (NUMERAL (BIT1 0)) x0) /\ True.
Definition term37 := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ~ (y0 = y1)) -> forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ~ (y0 = y1).
Definition term63 (x0 : nat) := (~ ((NUMERAL 0) = x0)) -> ((NUMERAL 0) = x0) = False.
Definition term1 := S (NUMERAL 0).
Definition term62 (x0 : nat) := ~ ((NUMERAL 0) = x0).
Definition term77 (x0 : nat) (x1 : nat) := Peano.lt (Nat.mul (NUMERAL (BIT1 0)) x1) (Nat.mul x0 x1).
Definition term26 := fun y0 : nat => (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term44 (x0 : nat) := (fun y0 : nat => (Nat.div (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term55 (x0 : nat) := (fun y0 : nat => (Nat.div y0 (NUMERAL (BIT1 0))) = y0) x0.
Definition term74 (x0 : nat) (x1 : nat) := Peano.lt (Nat.div x1 x0) x1.
Definition term45 (x0 : nat) := Nat.div (NUMERAL 0) x0.
Definition term73 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) -> (Peano.lt (Nat.div x1 x0) x1) = (Peano.lt x1 (Nat.mul x0 x1)).
Definition term88 (x0 : nat) := Peano.lt (NUMERAL (BIT1 0)) x0.
Definition term76 (x0 : nat) := Peano.lt (Nat.mul (NUMERAL (BIT1 0)) x0).
Definition term80 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (Nat.mul x0 y1) (Nat.mul y0 y1)) = ((Peano.lt x0 y0) /\ (~ (y1 = (NUMERAL 0))))) x1.
Definition term67 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.lt (Nat.div y0 x0) y1) = (Peano.lt y0 (Nat.mul x0 y1))) x1.
Definition term56 (x0 : nat) := Nat.div x0 (NUMERAL (BIT1 0)).
Definition term27 := fun y0 : nat => y0 = (Nat.mul (NUMERAL (BIT1 0)) y0).
Definition term95 (x0 : nat) := ~ ((x0 = (S (NUMERAL 0))) \/ (x0 = (NUMERAL 0))).
Definition term40 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term7 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term96 (x0 : nat) := forall y0 : nat, ((Nat.div x0 y0) = x0) = ((x0 = (NUMERAL 0)) \/ (y0 = (NUMERAL (BIT1 0)))).
Definition term2 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term64 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.div x1 x0) x1) -> ~ ((Nat.div x1 x0) = x1).
Definition term60 (x0 : nat) := (fun y0 : nat => (Nat.div y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term68 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (x1 = (NUMERAL 0))) -> (Peano.lt (Nat.div x0 x1) y0) = (Peano.lt x0 (Nat.mul x1 y0)).
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.div x0 x1) x2.
Definition term83 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term50 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term97 := forall y0 : nat, forall y1 : nat, ((Nat.div y0 y1) = y0) = ((y0 = (NUMERAL 0)) \/ (y1 = (NUMERAL (BIT1 0)))).
Definition term79 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.mul x0 y1) (Nat.mul y0 y1)) = ((Peano.lt x0 y0) /\ (~ (y1 = (NUMERAL 0)))).
Definition term66 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.lt (Nat.div y0 x0) y1) = (Peano.lt y0 (Nat.mul x0 y1)).
Definition term30 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ~ (y0 = y1).
Definition term11 := forall y0 : nat, forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1)).
Definition term10 := forall y0 : nat, forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1)).
Definition term9 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term92 (x0 : nat) := (x0 = (S (NUMERAL 0))) \/ (Peano.le x0 (NUMERAL 0)).
Definition term39 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term5 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term41 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL (BIT1 0))).
Definition term24 := forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0.
Definition term46 := Nat.div (NUMERAL 0).
Definition term13 (x0 : nat) := forall y0 : nat, (Peano.le x0 (S y0)) = ((x0 = (S y0)) \/ (Peano.le x0 y0)).
Definition term93 (x0 : nat) := or (x0 = (S (NUMERAL 0))).
Definition term29 (x0 : nat) := (fun y0 : nat => y0 = (Nat.mul (NUMERAL (BIT1 0)) y0)) x0.
Definition term32 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) -> ~ (x0 = y0).
Definition term89 (x0 : nat) := ~ (Peano.le x0 (NUMERAL (BIT1 0))).
Definition term94 (x0 : nat) := (x0 = (S (NUMERAL 0))) \/ (x0 = (NUMERAL 0)).
Definition term47 (x0 : nat) (x1 : nat) := @eq nat (Nat.div x0 x1).
Definition term85 (x0 : nat) (x1 : nat) := (Peano.lt (NUMERAL (BIT1 0)) x0) /\ (~ (x1 = (NUMERAL 0))).
Definition term16 (x0 : nat) (x1 : nat) := (x0 = (S x1)) \/ (Peano.le x0 x1).
Definition term57 := @eq nat (NUMERAL (BIT1 0)).
Definition term31 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> ~ (y0 = y1)) x0.
Definition term20 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1))) x0.
Definition term12 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 (S y1)) = ((y0 = (S y1)) \/ (Peano.le y0 y1))) x0.
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = (NUMERAL 0))) -> (Peano.lt (Nat.div x0 x1) x2) = (Peano.lt x0 (Nat.mul x1 x2)).
Definition term28 := forall y0 : nat, y0 = (Nat.mul (NUMERAL (BIT1 0)) y0).
Definition term84 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x1) /\ (~ (x2 = (NUMERAL 0))).
Definition term17 := forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term21 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt y0 x0) = (~ (Peano.le x0 y0))) x1.
Definition term91 (x0 : nat) := Peano.le x0 (S (NUMERAL 0)).
Definition term53 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term33 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) -> ~ (x0 = y0)) x1.
Definition term8 := fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1)).
Definition term49 (x0 : nat) (x1 : nat) := @eq Prop ((Nat.div x1 x0) = x1).
Definition term36 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> ~ (y0 = y1)) -> ~ (x0 = x1).
Definition term34 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) -> ~ (x0 = x1).
Definition term61 (x0 : nat) := Nat.div x0 (NUMERAL 0).
Definition term59 (x0 : nat) (x1 : nat) := ~ ((Nat.div x1 x0) = x1).
Definition term19 (x0 : nat) := Peano.le x0 (NUMERAL 0).
Definition term14 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 (S y0)) = ((x0 = (S y0)) \/ (Peano.le x0 y0))) x1.
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt x0 (Nat.mul x1 x2).
Definition term22 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term15 (x0 : nat) (x1 : nat) := Peano.le x0 (S x1).
Definition term52 (x0 : nat) := True \/ (x0 = (NUMERAL (BIT1 0))).
Definition term75 (x0 : nat) (x1 : nat) := Peano.lt x1 (Nat.mul x0 x1).
Definition term90 (x0 : nat) := Peano.le x0 (NUMERAL (BIT1 0)).
Definition term38 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term54 (x0 : nat) := False \/ (x0 = (NUMERAL (BIT1 0))).
Definition term0 := NUMERAL (BIT1 0).
Definition term25 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) x0.
Definition term86 (x0 : nat) := and (Peano.lt (NUMERAL (BIT1 0)) x0).
Definition term81 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.lt (Nat.mul x0 y0) (Nat.mul x1 y0)) = ((Peano.lt x0 x1) /\ (~ (y0 = (NUMERAL 0)))).
