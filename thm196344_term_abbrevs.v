Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term34 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1).
Definition term68 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> ((Nat.div x0 x1) = (NUMERAL 0)) = (Peano.lt x0 x1).
Definition term45 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term18 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (exists y3 : nat, (y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.div y0 y1) = y2) x0.
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.div y0 y1) = y2) x0.
Definition term32 (x0 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> forall y1 : nat, (y1 = (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0))) /\ (Peano.lt (Nat.modulo y1 y0) y0)) x0.
Definition term63 (x0 : nat) (x1 : nat) := exists y0 : nat, (x0 = (Nat.add (Nat.mul (NUMERAL 0) x1) y0)) /\ (Peano.lt y0 x1).
Definition term17 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.div y0 y1) = y2) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (exists y3 : nat, (y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.div y0 y1) = y2.
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, (x0 = (Nat.add (Nat.mul x2 x1) y0)) /\ (Peano.lt y0 x1)) -> (Nat.div x0 x1) = x2.
Definition term46 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (exists y1 : nat, (x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) -> (Nat.div x0 x1) = y0) x2.
Definition term38 (x0 : nat) (x1 : nat) := Peano.lt (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) x1.
Definition term27 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term60 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (NUMERAL 0) x0) x1.
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, (x0 = (Nat.add (Nat.mul x1 x2) y0)) /\ (Peano.lt y0 x2).
Definition term31 := (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> forall y1 : nat, (y1 = (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0))) /\ (Peano.lt (Nat.modulo y1 y0) y0).
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3).
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((x0 = (Nat.add (Nat.mul x2 x1) y0)) /\ (Peano.lt y0 x1)) -> (Nat.div x0 x1) = x2) x3.
Definition term52 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1).
Definition term33 (x0 : nat) (x1 : nat) := (fun y0 : nat => (y0 = (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0))) /\ (Peano.lt (Nat.modulo y0 x0) x0)) x1.
Definition term58 (x0 : nat) (x1 : nat) := (exists y0 : nat, (x0 = (Nat.add (Nat.mul (NUMERAL 0) x1) y0)) /\ (Peano.lt y0 x1)) -> (Nat.div x0 x1) = (NUMERAL 0).
Definition term19 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) -> (Nat.div x0 y0) = y1) x1.
Definition term26 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term54 (x0 : nat) (x1 : nat) := Nat.add (NUMERAL 0) (Nat.modulo x0 x1).
Definition term51 (x0 : nat) (x1 : nat) := Nat.mul (Nat.div x0 x1) x1.
Definition term56 (x0 : nat) (x1 : nat) := Peano.lt (Nat.modulo x0 x1).
Definition term65 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) -> (Nat.div x0 x1) = (NUMERAL 0).
Definition term30 := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> forall y1 : nat, (y1 = (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0))) /\ (Peano.lt (Nat.modulo y1 y0) y0).
Definition term40 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt x0 x1).
Definition term35 (x0 : nat) := fun y0 : nat => Peano.lt y0 x0.
Definition term59 (x0 : nat) := Nat.add (Nat.mul (NUMERAL 0) x0).
Definition term64 (x0 : nat) (x1 : nat) := fun y0 : nat => (x0 = (Nat.add (Nat.mul (NUMERAL 0) x1) y0)) /\ (Peano.lt y0 x1).
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x1 = (Nat.add (Nat.mul x3 x2) x0)) /\ (Peano.lt x0 x2)) -> (Nat.div x1 x2) = x3.
Definition term44 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((x0 = (Nat.add (Nat.mul x2 x1) y0)) /\ (Peano.lt y0 x1)) -> (Nat.div x0 x1) = x2.
Definition term21 := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term16 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (exists y3 : nat, (y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.div y0 y1) = y2.
Definition term15 (x0 : nat) := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) -> (Nat.div x0 y0) = y1.
Definition term4 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) -> (Nat.div x0 x1) = y0.
Definition term2 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) -> (Nat.div x0 y0) = y1.
Definition term0 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.div y0 y1) = y2.
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) -> (Nat.div x0 x1) = y0) x2.
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) -> (Nat.div x0 y0) = y1) x1.
Definition term39 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => Peano.lt y0 x0) x1).
Definition term36 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.lt y0 x0) x1.
Definition term25 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term42 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term43 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.div y0 y1) = y2) -> (Nat.div x0 x1) = x2.
Definition term66 (x0 : nat) (x1 : nat) := ((Nat.div x0 x1) = (NUMERAL 0)) -> Peano.lt x0 x1.
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (x0 = (Nat.add (Nat.mul x1 x2) y0)) /\ (Peano.lt y0 x2).
Definition term67 (x0 : nat) (x1 : nat) := (((Nat.div x0 x1) = (NUMERAL 0)) -> Peano.lt x0 x1) /\ ((Peano.lt x0 x1) -> (Nat.div x0 x1) = (NUMERAL 0)).
Definition term49 (x0 : nat) (x1 : nat) := Nat.mul (Nat.div x0 x1).
Definition term28 (x0 : nat) := forall y0 : nat, (y0 = (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0))) /\ (Peano.lt (Nat.modulo y0 x0) x0).
Definition term14 (x0 : nat) (x1 : nat) := forall y0 : nat, (exists y1 : nat, (x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) -> (Nat.div x0 x1) = y0.
Definition term53 := Nat.add (NUMERAL 0).
Definition term22 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) x0.
Definition term62 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (NUMERAL 0) x1) x0)) /\ (Peano.lt x0 x1).
Definition term57 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (Peano.lt (Nat.modulo x0 x1) x1) = True.
Definition term55 (x0 : nat) (x1 : nat) := Peano.lt (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)).
Definition term48 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term41 (x0 : nat) (x1 : nat) := Peano.lt (Nat.modulo x0 x1) x1.
Definition term24 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)) x1.
Definition term29 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> forall y0 : nat, (y0 = (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0))) /\ (Peano.lt (Nat.modulo y0 x0) x0).
Definition term50 := Nat.mul (NUMERAL 0).
Definition term47 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term61 (x0 : nat) (x1 : nat) := and (x1 = (Nat.add (Nat.mul (NUMERAL 0) x0) x1)).
Definition term69 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> ((Nat.div x0 y0) = (NUMERAL 0)) = (Peano.lt x0 y0).
Definition term23 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term37 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.lt y0 x1) (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)).
