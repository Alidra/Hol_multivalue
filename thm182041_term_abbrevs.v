Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term74 (x0 : nat) := and (x0 = (Nat.add (Nat.mul x0 (NUMERAL (BIT1 0))) (NUMERAL 0))).
Definition term63 := @eq Prop ((forall y0 : nat, (Nat.div y0 (NUMERAL (BIT1 0))) = y0) /\ (forall y0 : nat, (Nat.modulo y0 (NUMERAL (BIT1 0))) = (NUMERAL 0))).
Definition term62 := @eq Prop ((forall y0 : nat, (fun y1 : nat => (Nat.div y1 (NUMERAL (BIT1 0))) = y1) y0) /\ (forall y0 : nat, (fun y1 : nat => (Nat.modulo y1 (NUMERAL (BIT1 0))) = (NUMERAL 0)) y0)).
Definition term48 := fun y0 : nat => (Nat.modulo y0 (NUMERAL (BIT1 0))) = (NUMERAL 0).
Definition term46 := forall y0 : nat, ((fun y1 : nat => (Nat.div y1 (NUMERAL (BIT1 0))) = y1) y0) /\ ((fun y1 : nat => (Nat.modulo y1 (NUMERAL (BIT1 0))) = (NUMERAL 0)) y0).
Definition term14 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term35 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y1 = (Nat.add (Nat.mul y0 y2) y3)) /\ (Peano.lt y3 y2)) -> ((Nat.div y1 y2) = y0) /\ ((Nat.modulo y1 y2) = y3)) x0.
Definition term20 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> ((Nat.div y0 y1) = y2) /\ ((Nat.modulo y0 y1) = y3)) x0.
Definition term68 := fun y0 : nat => ((fun y1 : nat => (Nat.div y1 (NUMERAL (BIT1 0))) = y1) y0) /\ ((fun y1 : nat => (Nat.modulo y1 (NUMERAL (BIT1 0))) = (NUMERAL 0)) y0).
Definition term34 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> ((Nat.div y0 y1) = y2) /\ ((Nat.modulo y0 y1) = y3)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y1 = (Nat.add (Nat.mul y0 y2) y3)) /\ (Peano.lt y3 y2)) -> ((Nat.div y1 y2) = y0) /\ ((Nat.modulo y1 y2) = y3).
Definition term78 := S (NUMERAL 0).
Definition term45 := (forall y0 : nat, (fun y1 : nat => (Nat.div y1 (NUMERAL (BIT1 0))) = y1) y0) /\ (forall y0 : nat, (fun y1 : nat => (Nat.modulo y1 (NUMERAL (BIT1 0))) = (NUMERAL 0)) y0).
Definition term67 (x0 : nat) := ((Nat.div x0 (NUMERAL (BIT1 0))) = x0) /\ ((Nat.modulo x0 (NUMERAL (BIT1 0))) = (NUMERAL 0)).
Definition term66 (x0 : nat) := ((fun y0 : nat => (Nat.div y0 (NUMERAL (BIT1 0))) = y0) x0) /\ ((fun y0 : nat => (Nat.modulo y0 (NUMERAL (BIT1 0))) = (NUMERAL 0)) x0).
Definition term59 := forall y0 : nat, (fun y1 : nat => (Nat.modulo y1 (NUMERAL (BIT1 0))) = (NUMERAL 0)) y0.
Definition term70 := forall y0 : nat, ((Nat.div y0 (NUMERAL (BIT1 0))) = y0) /\ ((Nat.modulo y0 (NUMERAL (BIT1 0))) = (NUMERAL 0)).
Definition term73 (x0 : nat) := Nat.add (Nat.mul x0 (NUMERAL (BIT1 0))) (NUMERAL 0).
Definition term44 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((forall y1 : a0, x0 y1) /\ (forall y1 : a0, y0 y1)) = (forall y1 : a0, (x0 y1) /\ (y0 y1))) x1.
Definition term49 (x0 : nat) := (fun y0 : nat => (Nat.div y0 (NUMERAL (BIT1 0))) = y0) x0.
Definition term17 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) x0.
Definition term11 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term6 := forall y0 : nat, (Peano.lt y0 (NUMERAL 0)) = False.
Definition term75 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3).
Definition term41 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term12 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((x1 = (Nat.add (Nat.mul x0 x2) y0)) /\ (Peano.lt y0 x2)) -> ((Nat.div x1 x2) = x0) /\ ((Nat.modulo x1 x2) = y0)) x3.
Definition term50 (x0 : nat) := Nat.div x0 (NUMERAL (BIT1 0)).
Definition term77 := True /\ (Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0))).
Definition term5 (x0 : nat) (x1 : nat) := (x0 = x1) \/ (Peano.lt x0 x1).
Definition term65 (x0 : nat) := and ((Nat.div x0 (NUMERAL (BIT1 0))) = x0).
Definition term51 := fun y0 : nat => (fun y1 : nat => (Nat.div y1 (NUMERAL (BIT1 0))) = y1) y0.
Definition term53 := forall y0 : nat, (Nat.div y0 (NUMERAL (BIT1 0))) = y0.
Definition term16 := forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term10 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term56 (x0 : nat) := (fun y0 : nat => (Nat.modulo y0 (NUMERAL (BIT1 0))) = (NUMERAL 0)) x0.
Definition term69 := fun y0 : nat => ((Nat.div y0 (NUMERAL (BIT1 0))) = y0) /\ ((Nat.modulo y0 (NUMERAL (BIT1 0))) = (NUMERAL 0)).
Definition term7 (x0 : nat) := (fun y0 : nat => (Peano.lt y0 (NUMERAL 0)) = False) x0.
Definition term83 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term80 := Peano.lt (NUMERAL 0) (S (NUMERAL 0)).
Definition term61 := (forall y0 : nat, (Nat.div y0 (NUMERAL (BIT1 0))) = y0) /\ (forall y0 : nat, (Nat.modulo y0 (NUMERAL (BIT1 0))) = (NUMERAL 0)).
Definition term55 := and (forall y0 : nat, (Nat.div y0 (NUMERAL (BIT1 0))) = y0).
Definition term33 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y1 = (Nat.add (Nat.mul y0 y2) y3)) /\ (Peano.lt y3 y2)) -> ((Nat.div y1 y2) = y0) /\ ((Nat.modulo y1 y2) = y3).
Definition term32 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((y0 = (Nat.add (Nat.mul x0 y1) y2)) /\ (Peano.lt y2 y1)) -> ((Nat.div y0 y1) = x0) /\ ((Nat.modulo y0 y1) = y2).
Definition term31 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((x1 = (Nat.add (Nat.mul x0 y0) y1)) /\ (Peano.lt y1 y0)) -> ((Nat.div x1 y0) = x0) /\ ((Nat.modulo x1 y0) = y1).
Definition term23 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) -> ((Nat.div x0 x1) = y0) /\ ((Nat.modulo x0 x1) = y1).
Definition term21 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) -> ((Nat.div x0 y0) = y1) /\ ((Nat.modulo x0 y0) = y2).
Definition term19 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> ((Nat.div y0 y1) = y2) /\ ((Nat.modulo y0 y1) = y3).
Definition term0 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1)).
Definition term52 := forall y0 : nat, (fun y1 : nat => (Nat.div y1 (NUMERAL (BIT1 0))) = y1) y0.
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((x1 = (Nat.add (Nat.mul x0 y0) y1)) /\ (Peano.lt y1 y0)) -> ((Nat.div x1 y0) = x0) /\ ((Nat.modulo x1 y0) = y1)) x2.
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) -> ((Nat.div x0 x1) = y0) /\ ((Nat.modulo x0 x1) = y1)) x2.
Definition term36 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((y0 = (Nat.add (Nat.mul x0 y1) y2)) /\ (Peano.lt y2 y1)) -> ((Nat.div y0 y1) = x0) /\ ((Nat.modulo y0 y1) = y2)) x1.
Definition term22 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) -> ((Nat.div x0 y0) = y1) /\ ((Nat.modulo x0 y0) = y2)) x1.
Definition term79 := Peano.lt (NUMERAL 0).
Definition term4 (x0 : nat) (x1 : nat) := Peano.lt x0 (S x1).
Definition term39 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((forall y1 : a0, x0 y1) /\ (forall y1 : a0, y0 y1)) = (forall y1 : a0, (x0 y1) /\ (y0 y1)).
Definition term71 (x0 : nat) := ((x0 = (Nat.add (Nat.mul x0 (NUMERAL (BIT1 0))) (NUMERAL 0))) /\ (Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)))) -> ((Nat.div x0 (NUMERAL (BIT1 0))) = x0) /\ ((Nat.modulo x0 (NUMERAL (BIT1 0))) = (NUMERAL 0)).
Definition term57 (x0 : nat) := Nat.modulo x0 (NUMERAL (BIT1 0)).
Definition term38 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((forall y2 : a0, y0 y2) /\ (forall y2 : a0, y1 y2)) = (forall y2 : a0, (y0 y2) /\ (y1 y2))) x0.
Definition term2 (x0 : nat) := forall y0 : nat, (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0)).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x1 = (Nat.add (Nat.mul x0 x2) x3)) /\ (Peano.lt x3 x2)) -> ((Nat.div x1 x2) = x0) /\ ((Nat.modulo x1 x2) = x3).
Definition term43 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term15 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term9 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 (S y0)) = ((x0 = y0) \/ (Peano.lt x0 y0))) x1.
Definition term47 := fun y0 : nat => (Nat.div y0 (NUMERAL (BIT1 0))) = y0.
Definition term81 := ((NUMERAL 0) = (NUMERAL 0)) \/ (Peano.lt (NUMERAL 0) (NUMERAL 0)).
Definition term8 (x0 : nat) := Peano.lt x0 (NUMERAL 0).
Definition term18 (x0 : nat) := Nat.mul x0 (NUMERAL (BIT1 0)).
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 (S y1)) = ((y0 = y1) \/ (Peano.lt y0 y1))) x0.
Definition term60 := forall y0 : nat, (Nat.modulo y0 (NUMERAL (BIT1 0))) = (NUMERAL 0).
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((x1 = (Nat.add (Nat.mul x0 x2) y0)) /\ (Peano.lt y0 x2)) -> ((Nat.div x1 x2) = x0) /\ ((Nat.modulo x1 x2) = y0).
Definition term58 := fun y0 : nat => (fun y1 : nat => (Nat.modulo y1 (NUMERAL (BIT1 0))) = (NUMERAL 0)) y0.
Definition term76 (x0 : nat) := (x0 = (Nat.add (Nat.mul x0 (NUMERAL (BIT1 0))) (NUMERAL 0))) /\ (Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0))).
Definition term54 := and (forall y0 : nat, (fun y1 : nat => (Nat.div y1 (NUMERAL (BIT1 0))) = y1) y0).
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> ((Nat.div y0 y1) = y2) /\ ((Nat.modulo y0 y1) = y3)) -> ((Nat.div x1 x2) = x0) /\ ((Nat.modulo x1 x2) = x3).
Definition term42 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term64 (x0 : nat) := and ((fun y0 : nat => (Nat.div y0 (NUMERAL (BIT1 0))) = y0) x0).
Definition term82 := or ((NUMERAL 0) = (NUMERAL 0)).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.div x1 x2) = x0) /\ ((Nat.modulo x1 x2) = x3).
Definition term13 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term72 := NUMERAL (BIT1 0).
