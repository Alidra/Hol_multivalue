Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term33 (x0 : nat) (x1 : nat) := (True -> Peano.lt (Nat.modulo x0 x1) x1) /\ (True -> True -> ~ (x1 = (NUMERAL 0))).
Definition term10 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> ((Nat.div x0 x1) = (NUMERAL 0)) = (Peano.lt x0 x1).
Definition term18 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> x1 -> x2.
Definition term42 (x0 : nat) (x1 : nat) := (True -> (Peano.lt (Nat.modulo x0 x1) x1) /\ (~ (x1 = (NUMERAL 0)))) -> (((Peano.lt (Nat.modulo x0 x1) x1) /\ (~ (x1 = (NUMERAL 0)))) -> (Nat.div (Nat.modulo x0 x1) x1) = (NUMERAL 0)) -> True -> (Nat.div (Nat.modulo x0 x1) x1) = (NUMERAL 0).
Definition term12 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> ((Nat.div (Nat.modulo x0 x1) x1) = (NUMERAL 0)) = (Peano.lt (Nat.modulo x0 x1) x1).
Definition term40 (x0 : nat) (x1 : nat) := ((True /\ True) -> (Peano.lt (Nat.modulo x0 x1) x1) /\ (~ (x1 = (NUMERAL 0)))) -> True -> (Peano.lt (Nat.modulo x0 x1) x1) /\ (~ (x1 = (NUMERAL 0))).
Definition term22 (x0 : nat) (x1 : nat) := True -> Peano.lt (Nat.modulo x0 x1) x1.
Definition term26 (x0 : nat) := (~ False) -> ~ (x0 = (NUMERAL 0)).
Definition term16 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (Nat.div (Nat.modulo x0 x1) x1) = (NUMERAL 0).
Definition term24 (x0 : nat) := (x0 = (NUMERAL 0)) -> False.
Definition term46 (x0 : nat) (x1 : nat) := (True -> (Nat.div (Nat.modulo x0 x1) x1) = (NUMERAL 0)) -> True -> (Nat.div (Nat.modulo x0 x1) x1) = (NUMERAL 0).
Definition term9 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> ((Nat.div x0 y0) = (NUMERAL 0)) = (Peano.lt x0 y0)) x1.
Definition term20 (x0 : nat) (x1 : nat) := ((Peano.lt (Nat.modulo x0 x1) x1) /\ (~ (x1 = (NUMERAL 0)))) -> (Nat.div (Nat.modulo x0 x1) x1) = (NUMERAL 0).
Definition term14 (x0 : nat) (x1 : nat) := (((Nat.div (Nat.modulo x0 x1) x1) = (NUMERAL 0)) = (Peano.lt (Nat.modulo x0 x1) x1)) -> (Peano.lt (Nat.modulo x0 x1) x1) -> (Nat.div (Nat.modulo x0 x1) x1) = (NUMERAL 0).
Definition term47 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (Nat.div (Nat.modulo x0 y0) y0) = (NUMERAL 0).
Definition term0 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term17 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.modulo x0 x1) x1) -> (~ (x1 = (NUMERAL 0))) -> (Nat.div (Nat.modulo x0 x1) x1) = (NUMERAL 0).
Definition term13 (x0 : nat) (x1 : nat) := Nat.div (Nat.modulo x0 x1) x1.
Definition term21 (x0 : nat) (x1 : nat) := ((Peano.lt (Nat.modulo x0 x1) x1) = True) -> True -> Peano.lt (Nat.modulo x0 x1) x1.
Definition term48 := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (Nat.div (Nat.modulo y0 y1) y1) = (NUMERAL 0).
Definition term2 := forall y0 : nat, forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0))).
Definition term1 := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> ((Nat.div y0 y1) = (NUMERAL 0)) = (Peano.lt y0 y1).
Definition term25 (x0 : nat) := ((x0 = (NUMERAL 0)) -> False) -> (~ False) -> ~ (x0 = (NUMERAL 0)).
Definition term45 (x0 : nat) (x1 : nat) := (True -> (Nat.div (Nat.modulo x0 x1) x1) = (NUMERAL 0)) -> (Nat.div (Nat.modulo x0 x1) x1) = (NUMERAL 0).
Definition term23 (x0 : nat) := ((x0 = (NUMERAL 0)) = False) -> (x0 = (NUMERAL 0)) -> False.
Definition term32 (x0 : nat) := True -> True -> ~ (x0 = (NUMERAL 0)).
Definition term41 (x0 : nat) (x1 : nat) := True -> (Peano.lt (Nat.modulo x0 x1) x1) /\ (~ (x1 = (NUMERAL 0))).
Definition term36 := ((True /\ True) = True) -> True -> True /\ True.
Definition term35 (x0 : nat) (x1 : nat) := (True /\ True) -> (Peano.lt (Nat.modulo x0 x1) x1) /\ (~ (x1 = (NUMERAL 0))).
Definition term5 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt (Nat.modulo x0 y0) y0) = (~ (y0 = (NUMERAL 0)))) x1.
Definition term19 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) -> x2.
Definition term4 (x0 : nat) := forall y0 : nat, (Peano.lt (Nat.modulo x0 y0) y0) = (~ (y0 = (NUMERAL 0))).
Definition term43 (x0 : nat) (x1 : nat) := (((Peano.lt (Nat.modulo x0 x1) x1) /\ (~ (x1 = (NUMERAL 0)))) -> (Nat.div (Nat.modulo x0 x1) x1) = (NUMERAL 0)) -> True -> (Nat.div (Nat.modulo x0 x1) x1) = (NUMERAL 0).
Definition term7 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> ((Nat.div y0 y1) = (NUMERAL 0)) = (Peano.lt y0 y1)) x0.
Definition term3 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (Nat.modulo y0 y1) y1) = (~ (y1 = (NUMERAL 0)))) x0.
Definition term15 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.modulo x0 x1) x1) -> (Nat.div (Nat.modulo x0 x1) x1) = (NUMERAL 0).
Definition term37 := True -> True /\ True.
Definition term44 (x0 : nat) (x1 : nat) := True -> (Nat.div (Nat.modulo x0 x1) x1) = (NUMERAL 0).
Definition term30 (x0 : nat) := ((~ False) -> ~ (x0 = (NUMERAL 0))) -> True -> ~ (x0 = (NUMERAL 0)).
Definition term38 (x0 : nat) (x1 : nat) := (True -> True /\ True) -> ((True /\ True) -> (Peano.lt (Nat.modulo x0 x1) x1) /\ (~ (x1 = (NUMERAL 0)))) -> True -> (Peano.lt (Nat.modulo x0 x1) x1) /\ (~ (x1 = (NUMERAL 0))).
Definition term29 (x0 : nat) := (True -> ~ False) -> ((~ False) -> ~ (x0 = (NUMERAL 0))) -> True -> ~ (x0 = (NUMERAL 0)).
Definition term11 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term6 (x0 : nat) (x1 : nat) := Peano.lt (Nat.modulo x0 x1) x1.
Definition term31 (x0 : nat) := True -> ~ (x0 = (NUMERAL 0)).
Definition term8 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> ((Nat.div x0 y0) = (NUMERAL 0)) = (Peano.lt x0 y0).
Definition term28 := True -> ~ False.
Definition term34 (x0 : nat) (x1 : nat) := ((True -> Peano.lt (Nat.modulo x0 x1) x1) /\ (True -> True -> ~ (x1 = (NUMERAL 0)))) -> (True /\ True) -> (Peano.lt (Nat.modulo x0 x1) x1) /\ (~ (x1 = (NUMERAL 0))).
Definition term27 := ((~ False) = True) -> True -> ~ False.
Definition term39 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.modulo x0 x1) x1) /\ (~ (x1 = (NUMERAL 0))).
