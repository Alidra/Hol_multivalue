Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term44 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1).
Definition term68 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term93 := (~ False) -> False.
Definition term3 (x0 : nat) (x1 : nat) := (((~ (x0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term75 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term1 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term81 (x0 : Prop) := ~ (~ x0).
Definition term40 (x0 : nat) := forall y0 : nat, (y0 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term80 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term46 (x0 : nat) := fun y0 : nat => ((y0 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)))) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term58 (x0 : nat) (x1 : nat) := @eq Prop ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) \/ (x1 = (NUMERAL 0))).
Definition term65 (x0 : nat) := ~ (x0 = x0).
Definition term52 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))).
Definition term47 (x0 : nat) := forall y0 : nat, ((y0 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)))) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term86 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term62 (x0 : nat) (x1 : nat) := ~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))).
Definition term59 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term90 (x0 : nat) (x1 : nat) := ((x1 = (Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0))) /\ (x1 = x1)) -> (Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1.
Definition term84 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term11 (x0 : nat) (x1 : nat) := imp (~ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1)).
Definition term6 := ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term34 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term63 (x0 : Prop) := (~ x0) -> x0.
Definition term85 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = x0) /\ (x1 = x2).
Definition term51 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((y0 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)))) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 y0) y0))) x1.
Definition term39 (x0 : nat) := fun y0 : nat => (y0 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term14 (x0 : nat) := imp (~ (x0 = (NUMERAL 0))).
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term16 (x0 : nat) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)) = x0)) -> (forall y1 : nat, forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) -> (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)) -> False.
Definition term78 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term64 (x0 : nat) := (~ (x0 = x0)) -> x0 = x0.
Definition term56 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) \/ (x1 = (NUMERAL 0)).
Definition term73 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term28 (x0 : nat) := fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term9 := (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term57 (x0 : nat) (x1 : nat) := @eq Prop ((x1 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))).
Definition term71 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term32 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term30 := fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0).
Definition term37 (x0 : nat) (x1 : nat) := (~ (~ (x1 = (NUMERAL 0)))) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term96 (x0 : nat) (x1 : nat) := (~ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1)) -> False.
Definition term5 := (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term15 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term19 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)) = x0)) -> (forall y1 : nat, forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) -> ~ (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)).
Definition term18 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)) = x0)) -> (forall y1 : nat, forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) -> (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)) -> False.
Definition term4 (x0 : nat) (x1 : nat) := (((~ (x0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> ((~ (x0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term35 (x0 : nat) := or (~ (~ (x0 = (NUMERAL 0)))).
Definition term25 (x0 : nat) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term36 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term77 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term49 := forall y0 : nat, forall y1 : nat, ((y1 = (NUMERAL 0)) \/ (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)))) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term42 := forall y0 : nat, forall y1 : nat, (y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term31 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0).
Definition term23 := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0)) -> (forall y2 : nat, forall y3 : nat, (Nat.mul y2 y3) = (Nat.mul y3 y2)) -> ~ (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)).
Definition term22 := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0)) -> (forall y2 : nat, forall y3 : nat, (Nat.mul y2 y3) = (Nat.mul y3 y2)) -> (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)) -> False.
Definition term7 := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term60 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)).
Definition term91 (x0 : nat) (x1 : nat) := (~ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1)) -> (Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1.
Definition term24 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term29 (x0 : nat) := forall y0 : nat, (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term54 (x0 : nat) := (x0 = (NUMERAL 0)) -> ~ (x0 = (NUMERAL 0)).
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term83 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term94 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0)) -> (forall y2 : nat, forall y3 : nat, (Nat.mul y2 y3) = (Nat.mul y3 y2)) -> (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)) -> False) x0.
Definition term50 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((y1 = (NUMERAL 0)) \/ (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)))) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo y0 y1) y1))) x0.
Definition term13 (x0 : nat) (x1 : nat) := (~ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term95 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)) = x0)) -> (forall y1 : nat, forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) -> (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)) -> False) x1.
Definition term43 (x0 : nat) (x1 : nat) := ((x1 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) /\ ((x1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term79 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term17 (x0 : nat) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)) = x0)) -> (forall y1 : nat, forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) -> ~ (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)).
Definition term61 (x0 : nat) (x1 : nat) := (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)).
Definition term2 (x0 : nat) (x1 : nat) := ((~ (x0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term10 := (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term45 (x0 : nat) (x1 : nat) := Peano.lt (Nat.modulo x0 x1) x1.
Definition term92 (x0 : nat) (x1 : nat) := ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1) -> False.
Definition term87 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term89 (x0 : nat) (x1 : nat) := (x1 = (Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0))) /\ (x1 = x1).
Definition term12 (x0 : nat) (x1 : nat) := (~ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term38 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term66 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term33 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term82 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term26 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term69 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term8 := imp (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)).
Definition term88 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term48 := fun y0 : nat => forall y1 : nat, ((y1 = (NUMERAL 0)) \/ (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)))) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term41 := fun y0 : nat => forall y1 : nat, (y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term27 := fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term21 := fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0)) -> (forall y2 : nat, forall y3 : nat, (Nat.mul y2 y3) = (Nat.mul y3 y2)) -> ~ (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)).
Definition term20 := fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0)) -> (forall y2 : nat, forall y3 : nat, (Nat.mul y2 y3) = (Nat.mul y3 y2)) -> (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)) -> False.
Definition term55 (x0 : Prop) := x0 -> ~ x0.
Definition term0 (x0 : nat) (x1 : nat) := ~ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1).
