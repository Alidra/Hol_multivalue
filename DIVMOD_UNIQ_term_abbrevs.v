Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := (((x0 = (Nat.add (Nat.mul x2 x1) x4)) /\ (Peano.lt x4 x1)) /\ ((x0 = (Nat.add (Nat.mul x3 x1) x5)) /\ (Peano.lt x5 x1))) -> (x2 = x3) /\ (x4 = x5).
Definition term2 (x0 : nat) := fun y0 : nat => (Peano.lt y0 x0) = (~ (Peano.le x0 y0)).
Definition term4 (x0 : nat) := forall y0 : nat, (Peano.lt y0 x0) = (~ (Peano.le x0 y0)).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (fun y0 : nat => forall y1 : nat, (((x0 = (Nat.add (Nat.mul x2 x1) x3)) /\ (Peano.lt x3 x1)) /\ ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1))) -> (x2 = y0) /\ (x3 = y1)) x4.
Definition term32 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = x1) /\ (x2 = x3).
Definition term44 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, (exists y4 : nat, exists y5 : nat, ((y4 = (Nat.add (Nat.mul y0 y5) y2)) /\ (Peano.lt y2 y5)) /\ ((y4 = (Nat.add (Nat.mul y1 y5) y3)) /\ (Peano.lt y3 y5))) -> (y0 = y1) /\ (y2 = y3)) x0.
Definition term19 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, forall y5 : nat, (((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) /\ ((y0 = (Nat.add (Nat.mul y4 y1) y5)) /\ (Peano.lt y5 y1))) -> (y2 = y4) /\ (y3 = y5)) x0.
Definition term1 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term31 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := ((x2 = (Nat.add (Nat.mul x0 x5) x1)) /\ (Peano.lt x1 x5)) /\ ((x2 = (Nat.add (Nat.mul x3 x5) x4)) /\ (Peano.lt x4 x5)).
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := fun y0 : nat => exists y1 : nat, ((y0 = (Nat.add (Nat.mul (Nat.div x0 x1) y1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) y1)) /\ ((y0 = (Nat.add (Nat.mul x2 y1) x3)) /\ (Peano.lt x3 y1)).
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := fun y0 : nat => exists y1 : nat, ((y0 = (Nat.add (Nat.mul x0 y1) x1)) /\ (Peano.lt x1 y1)) /\ ((y0 = (Nat.add (Nat.mul x2 y1) x3)) /\ (Peano.lt x3 y1)).
Definition term43 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, forall y5 : nat, (((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) /\ ((y0 = (Nat.add (Nat.mul y4 y1) y5)) /\ (Peano.lt y5 y1))) -> (y2 = y4) /\ (y3 = y5)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, (exists y4 : nat, exists y5 : nat, ((y4 = (Nat.add (Nat.mul y0 y5) y2)) /\ (Peano.lt y2 y5)) /\ ((y4 = (Nat.add (Nat.mul y1 y5) y3)) /\ (Peano.lt y3 y5))) -> (y0 = y1) /\ (y2 = y3).
Definition term17 := (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.add (Nat.mul x0 x3) x2) = x1) /\ (Peano.lt x2 x3).
Definition term57 (x0 : nat) := (fun y0 : nat => Peano.le (NUMERAL 0) y0) x0.
Definition term15 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term64 (x0 : nat) := (x0 = (NUMERAL 0)) -> False.
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3).
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := fun y0 : nat => ((x2 = (Nat.add (Nat.mul x0 y0) x1)) /\ (Peano.lt x1 y0)) /\ ((x2 = (Nat.add (Nat.mul x3 y0) x4)) /\ (Peano.lt x4 y0)).
Definition term55 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x0 = (Nat.add (Nat.mul (Nat.div x0 x3) x3) (Nat.modulo x0 x3))) /\ (Peano.lt (Nat.modulo x0 x3) x3)) /\ ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3)).
Definition term14 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term5 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term54 (x0 : nat) (x1 : nat) := and ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term0 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term65 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := exists y0 : nat, ((x1 = (Nat.add (Nat.mul (Nat.div x1 x0) y0) (Nat.modulo x1 x0))) /\ (Peano.lt (Nat.modulo x1 x0) y0)) /\ ((x1 = (Nat.add (Nat.mul x2 y0) x3)) /\ (Peano.lt x3 y0)).
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := exists y0 : nat, ((x2 = (Nat.add (Nat.mul x0 y0) x1)) /\ (Peano.lt x1 y0)) /\ ((x2 = (Nat.add (Nat.mul x3 y0) x4)) /\ (Peano.lt x4 y0)).
Definition term56 (x0 : nat) (x1 : nat) := ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)) /\ True.
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := and (x0 = (Nat.add (Nat.mul x1 x2) x3)).
Definition term74 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> ((Nat.div y0 y1) = y2) /\ ((Nat.modulo y0 y1) = y3).
Definition term73 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) -> ((Nat.div x0 y0) = y1) /\ ((Nat.modulo x0 y0) = y2).
Definition term72 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) -> ((Nat.div x0 x1) = y0) /\ ((Nat.modulo x0 x1) = y1).
Definition term42 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, (exists y4 : nat, exists y5 : nat, ((y4 = (Nat.add (Nat.mul y0 y5) y2)) /\ (Peano.lt y2 y5)) /\ ((y4 = (Nat.add (Nat.mul y1 y5) y3)) /\ (Peano.lt y3 y5))) -> (y0 = y1) /\ (y2 = y3).
Definition term41 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, (exists y3 : nat, exists y4 : nat, ((y3 = (Nat.add (Nat.mul x0 y4) y1)) /\ (Peano.lt y1 y4)) /\ ((y3 = (Nat.add (Nat.mul y0 y4) y2)) /\ (Peano.lt y2 y4))) -> (x0 = y0) /\ (y1 = y2).
Definition term40 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, (exists y2 : nat, exists y3 : nat, ((y2 = (Nat.add (Nat.mul x0 y3) y0)) /\ (Peano.lt y0 y3)) /\ ((y2 = (Nat.add (Nat.mul x1 y3) y1)) /\ (Peano.lt y1 y3))) -> (x0 = x1) /\ (y0 = y1).
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := forall y0 : nat, forall y1 : nat, (((x0 = (Nat.add (Nat.mul x2 x1) x3)) /\ (Peano.lt x3 x1)) /\ ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1))) -> (x2 = y0) /\ (x3 = y1).
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, (((x0 = (Nat.add (Nat.mul x2 x1) y0)) /\ (Peano.lt y0 x1)) /\ ((x0 = (Nat.add (Nat.mul y1 x1) y2)) /\ (Peano.lt y2 x1))) -> (x2 = y1) /\ (y0 = y2).
Definition term22 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, (((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) /\ ((x0 = (Nat.add (Nat.mul y2 x1) y3)) /\ (Peano.lt y3 x1))) -> (y0 = y2) /\ (y1 = y3).
Definition term20 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (((x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) /\ ((x0 = (Nat.add (Nat.mul y3 y0) y4)) /\ (Peano.lt y4 y0))) -> (y1 = y3) /\ (y2 = y4).
Definition term18 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, forall y5 : nat, (((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) /\ ((y0 = (Nat.add (Nat.mul y4 y1) y5)) /\ (Peano.lt y5 y1))) -> (y2 = y4) /\ (y3 = y5).
Definition term9 := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term8 := forall y0 : nat, forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1)).
Definition term7 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term61 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) -> False.
Definition term46 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, exists y3 : nat, ((y2 = (Nat.add (Nat.mul x0 y3) y0)) /\ (Peano.lt y0 y3)) /\ ((y2 = (Nat.add (Nat.mul x1 y3) y1)) /\ (Peano.lt y1 y3))) -> (x0 = x1) /\ (y0 = y1)) x2.
Definition term3 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term45 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (exists y3 : nat, exists y4 : nat, ((y3 = (Nat.add (Nat.mul x0 y4) y1)) /\ (Peano.lt y1 y4)) /\ ((y3 = (Nat.add (Nat.mul y0 y4) y2)) /\ (Peano.lt y2 y4))) -> (x0 = y0) /\ (y1 = y2)) x1.
Definition term21 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (((x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) /\ ((x0 = (Nat.add (Nat.mul y3 y0) y4)) /\ (Peano.lt y4 y0))) -> (y1 = y3) /\ (y2 = y4)) x1.
Definition term13 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (exists y0 : nat, exists y1 : nat, ((y0 = (Nat.add (Nat.mul x0 y1) x2)) /\ (Peano.lt x2 y1)) /\ ((y0 = (Nat.add (Nat.mul x1 y1) x3)) /\ (Peano.lt x3 y1))) -> (x0 = x1) /\ (x2 = x3).
Definition term58 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x1 = (Nat.add (Nat.mul x0 x2) x3)) /\ (Peano.lt x3 x2)) -> ((Nat.div x1 x2) = x0) /\ ((Nat.modulo x1 x2) = x3).
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, forall y5 : nat, (((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) /\ ((y0 = (Nat.add (Nat.mul y4 y1) y5)) /\ (Peano.lt y5 y1))) -> (y2 = y4) /\ (y3 = y5)) -> (x0 = x1) /\ (x2 = x3).
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, (((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) /\ ((x0 = (Nat.add (Nat.mul y2 x1) y3)) /\ (Peano.lt y3 x1))) -> (y0 = y2) /\ (y1 = y3)) x2.
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := (fun y0 : nat => (((x0 = (Nat.add (Nat.mul x2 x1) x4)) /\ (Peano.lt x4 x1)) /\ ((x0 = (Nat.add (Nat.mul x3 x1) y0)) /\ (Peano.lt y0 x1))) -> (x2 = x3) /\ (x4 = y0)) x5.
Definition term62 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, (exists y1 : nat, exists y2 : nat, ((y1 = (Nat.add (Nat.mul x0 y2) x2)) /\ (Peano.lt x2 y2)) /\ ((y1 = (Nat.add (Nat.mul x1 y2) y0)) /\ (Peano.lt y0 y2))) -> (x0 = x1) /\ (x2 = y0).
Definition term59 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1))) x0.
Definition term10 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) x0.
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (((x0 = (Nat.add (Nat.mul x2 x1) y0)) /\ (Peano.lt y0 x1)) /\ ((x0 = (Nat.add (Nat.mul y1 x1) y2)) /\ (Peano.lt y2 x1))) -> (x2 = y1) /\ (y0 = y2)) x3.
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((x1 = (Nat.add (Nat.mul x0 x2) y0)) /\ (Peano.lt y0 x2)) -> ((Nat.div x1 x2) = x0) /\ ((Nat.modulo x1 x2) = y0).
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := forall y0 : nat, (((x0 = (Nat.add (Nat.mul x2 x1) x4)) /\ (Peano.lt x4 x1)) /\ ((x0 = (Nat.add (Nat.mul x3 x1) y0)) /\ (Peano.lt y0 x1))) -> (x2 = x3) /\ (x4 = y0).
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (exists y0 : nat, exists y1 : nat, ((y0 = (Nat.add (Nat.mul (Nat.div x1 x2) y1) (Nat.modulo x1 x2))) /\ (Peano.lt (Nat.modulo x1 x2) y1)) /\ ((y0 = (Nat.add (Nat.mul x0 y1) x3)) /\ (Peano.lt x3 y1))) -> ((Nat.div x1 x2) = x0) /\ ((Nat.modulo x1 x2) = x3).
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := and ((Nat.add (Nat.mul x0 x1) x2) = x3).
Definition term16 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term60 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt y0 x0) = (~ (Peano.le x0 y0))) x1.
Definition term12 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)) x1.
Definition term47 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => (exists y1 : nat, exists y2 : nat, ((y1 = (Nat.add (Nat.mul x0 y2) x2)) /\ (Peano.lt x2 y2)) /\ ((y1 = (Nat.add (Nat.mul x1 y2) y0)) /\ (Peano.lt y0 y2))) -> (x0 = x1) /\ (x2 = y0)) x3.
Definition term6 := fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1)).
Definition term66 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := fun y0 : nat => ((x1 = (Nat.add (Nat.mul (Nat.div x1 x0) y0) (Nat.modulo x1 x0))) /\ (Peano.lt (Nat.modulo x1 x0) y0)) /\ ((x1 = (Nat.add (Nat.mul x2 y0) x3)) /\ (Peano.lt x3 y0)).
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := exists y0 : nat, exists y1 : nat, ((y0 = (Nat.add (Nat.mul (Nat.div x0 x1) y1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) y1)) /\ ((y0 = (Nat.add (Nat.mul x2 y1) x3)) /\ (Peano.lt x3 y1)).
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := exists y0 : nat, exists y1 : nat, ((y0 = (Nat.add (Nat.mul x0 y1) x1)) /\ (Peano.lt x1 y1)) /\ ((y0 = (Nat.add (Nat.mul x2 y1) x3)) /\ (Peano.lt x3 y1)).
Definition term63 := Peano.le (NUMERAL 0).
Definition term49 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x1) x2.
Definition term11 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.div x1 x2) = x0) /\ ((Nat.modulo x1 x2) = x3).
