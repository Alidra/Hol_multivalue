Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term53 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1).
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0))) x2.
Definition term57 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 (Nat.mul (Nat.div x1 x2) x2)) (Nat.mul x0 (Nat.modulo x1 x2)).
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) := ((x2 = (Nat.add (Nat.mul (Nat.div x2 x0) x0) (Nat.modulo x2 x0))) /\ (Peano.lt (Nat.modulo x2 x0) x0)) -> Peano.le (Nat.mul x0 (Nat.mul x1 (Nat.div x2 x0))) (Nat.mul x1 x2).
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 (Nat.mul x2 (Nat.div x1 x2))) (Nat.add (Nat.mul x0 (Nat.mul x2 (Nat.div x1 x2))) (Nat.mul x0 (Nat.modulo x1 x2))).
Definition term41 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le y2 (Nat.div y1 y0)) = (Peano.le (Nat.mul y0 y2) y1)) x0.
Definition term5 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul y0 (Nat.add y1 y2)) = (Nat.add (Nat.mul y0 y1) (Nat.mul y0 y2))) x0.
Definition term23 (x0 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> forall y1 : nat, (y1 = (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0))) /\ (Peano.lt (Nat.modulo y1 y0) y0)) x0.
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 (Nat.mul x2 (Nat.div x1 x2))) (Nat.mul x0 (Nat.modulo x1 x2)).
Definition term62 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.mul x2 (Nat.div x1 x2)).
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.div x1 x2).
Definition term66 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 (Nat.mul (Nat.div x1 x2) x2)).
Definition term36 (x0 : nat) (x1 : nat) := Nat.div (Nat.mul x0 x1).
Definition term18 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term56 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x2 (Nat.mul x0 (Nat.div x1 x2))) (Nat.mul x0 (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2))).
Definition term22 := (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> forall y1 : nat, (y1 = (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0))) /\ (Peano.lt (Nat.modulo y1 y0) y0).
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 (Nat.mul x2 (Nat.div x1 x2))).
Definition term1 (x0 : nat) := forall y0 : nat, Peano.le x0 (Nat.add x0 y0).
Definition term54 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add (Nat.mul (Nat.div x1 x2) x2) (Nat.modulo x1 x2)).
Definition term52 (x0 : nat) (x1 : nat) := (fun y0 : nat => (y0 = (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0))) /\ (Peano.lt (Nat.modulo y0 x0) x0)) x1.
Definition term43 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le y1 (Nat.div y0 x0)) = (Peano.le (Nat.mul x0 y1) y0)) x1.
Definition term7 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1))) x1.
Definition term17 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.div (Nat.mul x0 x1) x2.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le x0 (Nat.add x0 y0)) x1.
Definition term58 (x0 : nat) (x1 : nat) := Nat.mul (Nat.div x0 x1) x1.
Definition term32 (x0 : nat) := (fun y0 : nat => Peano.le y0 y0) x0.
Definition term30 (x0 : nat) := (fun y0 : nat => (Nat.div y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term28 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 (Nat.mul x1 (Nat.div x2 x0))) (Nat.mul x1 x2).
Definition term21 := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> forall y1 : nat, (y1 = (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0))) /\ (Peano.lt (Nat.modulo y1 y0) y0).
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term74 := forall y0 : nat, forall y1 : nat, forall y2 : nat, Peano.le (Nat.mul y0 (Nat.div y1 y2)) (Nat.div (Nat.mul y0 y1) y2).
Definition term73 (x0 : nat) := forall y0 : nat, forall y1 : nat, Peano.le (Nat.mul x0 (Nat.div y0 y1)) (Nat.div (Nat.mul x0 y0) y1).
Definition term42 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le y1 (Nat.div y0 x0)) = (Peano.le (Nat.mul x0 y1) y0).
Definition term12 := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term6 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul x0 (Nat.add y0 y1)) = (Nat.add (Nat.mul x0 y0) (Nat.mul x0 y1)).
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.modulo x1 x2).
Definition term25 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term72 (x0 : nat) (x1 : nat) := forall y0 : nat, Peano.le (Nat.mul x0 (Nat.div x1 y0)) (Nat.div (Nat.mul x0 x1) y0).
Definition term16 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 (Nat.div x1 x2)).
Definition term45 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (x0 = (NUMERAL 0))) -> (Peano.le y0 (Nat.div x1 x0)) = (Peano.le (Nat.mul x0 y0) x1)) x2.
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 x1) x2.
Definition term8 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul x1 (Nat.add x0 y0)) = (Nat.add (Nat.mul x1 x0) (Nat.mul x1 y0)).
Definition term64 (x0 : nat) (x1 : nat) := Nat.mul x1 (Nat.div x0 x1).
Definition term19 (x0 : nat) := forall y0 : nat, (y0 = (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0))) /\ (Peano.lt (Nat.modulo y0 x0) x0).
Definition term3 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.add x0 x1).
Definition term13 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) x0.
Definition term46 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) -> (Peano.le x1 (Nat.div x2 x0)) = (Peano.le (Nat.mul x0 x1) x2).
Definition term47 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le x0 (Nat.div x1 x2).
Definition term27 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term60 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.mul x1 x2).
Definition term55 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x2 (Nat.mul x0 (Nat.div x1 x2))).
Definition term65 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.mul (Nat.div x1 x2) x2).
Definition term61 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x2 (Nat.mul x0 (Nat.div x1 x2)).
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) -> (Peano.le (Nat.mul x1 (Nat.div x2 x0)) (Nat.div (Nat.mul x1 x2) x0)) = (Peano.le (Nat.mul x0 (Nat.mul x1 (Nat.div x2 x0))) (Nat.mul x1 x2)).
Definition term59 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x2 (Nat.mul x0 (Nat.div x1 x2))) (Nat.add (Nat.mul x0 (Nat.mul (Nat.div x1 x2) x2)) (Nat.mul x0 (Nat.modulo x1 x2))).
Definition term29 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term63 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 (Nat.mul x2 (Nat.div x1 x2))).
Definition term49 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term15 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)) x1.
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.mul (Nat.mul x1 x0) x2) = (Nat.mul x1 (Nat.mul x0 x2))) /\ ((Nat.mul x1 (Nat.mul x0 x2)) = (Nat.mul x0 (Nat.mul x1 x2))).
Definition term20 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> forall y0 : nat, (y0 = (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0))) /\ (Peano.lt (Nat.modulo y0 x0) x0).
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.add x1 x2).
Definition term35 := Peano.le (NUMERAL 0).
Definition term44 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le y0 (Nat.div x1 x0)) = (Peano.le (Nat.mul x0 y0) x1).
Definition term14 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term31 (x0 : nat) := Nat.div x0 (NUMERAL 0).
Definition term26 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term24 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term38 (x0 : nat) (x1 : nat) := Nat.div (Nat.mul x0 x1) (NUMERAL 0).
Definition term40 := Peano.le (NUMERAL 0) (NUMERAL 0).
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 (Nat.div x1 x2)) (Nat.div (Nat.mul x0 x1) x2).
