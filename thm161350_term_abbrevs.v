Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term47 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1).
Definition term113 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x1) /\ (~ (x1 = x2)).
Definition term97 (x0 : nat) (x1 : nat) := (((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1))) /\ ((Nat.modulo x0 x1) = (Nat.modulo x0 x1))) -> (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)).
Definition term74 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term135 := (~ False) -> False.
Definition term6 (x0 : nat) (x1 : nat) := (((~ (x0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term125 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term114 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x0 = x1)) \/ (x1 = x2))).
Definition term4 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term92 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = x1) /\ (x2 = x3).
Definition term88 (x0 : Prop) := ~ (~ x0).
Definition term99 (x0 : nat) (x1 : nat) := ~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))).
Definition term43 (x0 : nat) := forall y0 : nat, (y0 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term60 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x3)) \/ ((Nat.add x0 x1) = (Nat.add x2 x3)).
Definition term87 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (~ (x0 = x1))) /\ (~ (~ (x2 = x3))).
Definition term129 (x0 : nat) (x1 : nat) := ((x0 = x0) /\ (~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = x0))) -> ~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))).
Definition term131 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) -> ~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))).
Definition term80 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop (((Nat.add x0 x2) = (Nat.add x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term49 (x0 : nat) := fun y0 : nat => ((y0 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)))) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term65 (x0 : nat) := ~ (x0 = x0).
Definition term117 (x0 : nat) (x1 : nat) := ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = (Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0))) /\ (~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term57 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))).
Definition term50 (x0 : nat) := forall y0 : nat, ((y0 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)))) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term93 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp (~ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term130 (x0 : nat) (x1 : nat) := ~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))).
Definition term124 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) /\ (~ (x1 = x2)).
Definition term70 (x0 : nat) (x1 : nat) := ~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1))).
Definition term81 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term91 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term14 (x0 : nat) (x1 : nat) := imp (~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)).
Definition term9 := ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term37 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term66 (x0 : Prop) := (~ x0) -> x0.
Definition term56 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((y0 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)))) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 y0) y0))) x1.
Definition term94 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((x0 = x1) /\ (x2 = x3)).
Definition term42 (x0 : nat) := fun y0 : nat => (y0 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term95 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x0 = x2) /\ (x1 = x3)) -> (Nat.add x0 x1) = (Nat.add x2 x3).
Definition term17 (x0 : nat) := imp (~ (x0 = (NUMERAL 0))).
Definition term19 (x0 : nat) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul y0 (Nat.div x0 y0)) (Nat.modulo x0 y0)) = x0)) -> (forall y1 : nat, forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) -> (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)) -> False.
Definition term134 (x0 : nat) := (x0 = (NUMERAL 0)) -> False.
Definition term85 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term64 (x0 : nat) := (~ (x0 = x0)) -> x0 = x0.
Definition term106 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term31 (x0 : nat) := fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term108 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x2)) \/ ((~ (x0 = x1)) \/ (x1 = x2)).
Definition term107 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term12 := (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term132 (x0 : nat) (x1 : nat) := (~ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) -> x1 = (NUMERAL 0).
Definition term77 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term78 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.add x0 x2) = (Nat.add x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term35 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term127 (x0 : nat) (x1 : nat) (x2 : nat) := ((x1 = x0) /\ (~ (x2 = x0))) -> ~ (x1 = x2).
Definition term116 (x0 : nat) (x1 : nat) (x2 : nat) := ((x1 = x0) /\ (~ (x0 = x2))) -> ~ (x1 = x2).
Definition term33 := fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0).
Definition term40 (x0 : nat) (x1 : nat) := (~ (~ (x1 = (NUMERAL 0)))) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term73 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.add x0 x2) = (Nat.add x1 x3)) \/ (~ (x2 = x3)).
Definition term1 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1).
Definition term67 (x0 : nat) (x1 : nat) := Nat.mul (Nat.div x0 x1) x1.
Definition term71 (x0 : nat) (x1 : nat) := (~ ((Nat.modulo x0 x1) = (Nat.modulo x0 x1))) -> (Nat.modulo x0 x1) = (Nat.modulo x0 x1).
Definition term63 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term105 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term2 (x0 : nat) (x1 : nat) := (~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)) -> False.
Definition term69 (x0 : nat) (x1 : nat) := (~ ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)))) -> (Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1)).
Definition term8 := (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term18 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term133 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> x0 = (NUMERAL 0).
Definition term22 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul y0 (Nat.div x0 y0)) (Nat.modulo x0 y0)) = x0)) -> (forall y1 : nat, forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) -> ~ (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)).
Definition term21 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul y0 (Nat.div x0 y0)) (Nat.modulo x0 y0)) = x0)) -> (forall y1 : nat, forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) -> (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)) -> False.
Definition term82 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((~ (x0 = x2)) \/ (~ (x1 = x3)))) -> (Nat.add x0 x1) = (Nat.add x2 x3).
Definition term7 (x0 : nat) (x1 : nat) := (((~ (x0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> ((~ (x0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term38 (x0 : nat) := or (~ (~ (x0 = (NUMERAL 0)))).
Definition term28 (x0 : nat) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term39 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term84 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term52 := forall y0 : nat, forall y1 : nat, ((y1 = (NUMERAL 0)) \/ (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)))) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term45 := forall y0 : nat, forall y1 : nat, (y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term34 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0).
Definition term26 := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> (forall y2 : nat, forall y3 : nat, (Nat.mul y2 y3) = (Nat.mul y3 y2)) -> ~ (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)).
Definition term25 := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> (forall y2 : nat, forall y3 : nat, (Nat.mul y2 y3) = (Nat.mul y3 y2)) -> (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)) -> False.
Definition term10 := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term121 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x1 = x0)) \/ (x2 = x0))) -> ~ (x1 = x2).
Definition term109 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x1 = x0)) \/ (x0 = x2))) -> ~ (x1 = x2).
Definition term79 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((Nat.add x0 x1) = (Nat.add x2 x3)))).
Definition term110 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x1)) \/ (x1 = x2).
Definition term27 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term58 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x1 = x3) -> (Nat.add x0 x1) = (Nat.add x2 x3).
Definition term103 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term68 (x0 : nat) (x1 : nat) := Nat.mul x1 (Nat.div x0 x1).
Definition term32 (x0 : nat) := forall y0 : nat, (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term115 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x0 = x1) /\ (~ (x1 = x2))).
Definition term104 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term128 (x0 : nat) (x1 : nat) := (x1 = x1) /\ (~ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1)).
Definition term54 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0)) x1.
Definition term90 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term123 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x0 = x2))) /\ (~ (x1 = x2)).
Definition term112 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x0 = x1))) /\ (~ (x1 = x2)).
Definition term72 (x0 : nat) (x1 : nat) := ~ ((Nat.modulo x0 x1) = (Nat.modulo x0 x1)).
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x1)) \/ (((Nat.add x0 x2) = (Nat.add x1 x3)) \/ (~ (x2 = x3))).
Definition term136 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> (forall y2 : nat, forall y3 : nat, (Nat.mul y2 y3) = (Nat.mul y3 y2)) -> (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)) -> False) x0.
Definition term55 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((y1 = (NUMERAL 0)) \/ (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)))) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo y0 y1) y1))) x0.
Definition term53 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) x0.
Definition term16 (x0 : nat) (x1 : nat) := (~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term98 (x0 : nat) (x1 : nat) := (~ ((Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)))) -> (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)).
Definition term137 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul y0 (Nat.div x0 y0)) (Nat.modulo x0 y0)) = x0)) -> (forall y1 : nat, forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) -> (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)) -> False) x1.
Definition term46 (x0 : nat) (x1 : nat) := ((x1 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) /\ ((x1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term86 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term20 (x0 : nat) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul y0 (Nat.div x0 y0)) (Nat.modulo x0 y0)) = x0)) -> (forall y1 : nat, forall y2 : nat, (Nat.mul y1 y2) = (Nat.mul y2 y1)) -> ~ (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)).
Definition term61 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = x2) -> (~ (x1 = x3)) \/ ((Nat.add x0 x1) = (Nat.add x2 x3)).
Definition term5 (x0 : nat) (x1 : nat) := ((~ (x0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x0 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term13 := (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term59 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term48 (x0 : nat) (x1 : nat) := Peano.lt (Nat.modulo x0 x1) x1.
Definition term83 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x1)) \/ (~ (x2 = x3)).
Definition term96 (x0 : nat) (x1 : nat) := ((Nat.mul (Nat.div x0 x1) x1) = (Nat.mul x1 (Nat.div x0 x1))) /\ ((Nat.modulo x0 x1) = (Nat.modulo x0 x1)).
Definition term62 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((Nat.add x0 x1) = (Nat.add x2 x3))).
Definition term15 (x0 : nat) (x1 : nat) := (~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)) -> (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term41 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term102 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term36 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term89 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term29 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term75 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term120 (x0 : nat) (x1 : nat) := ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1) -> ~ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1).
Definition term100 (x0 : nat) (x1 : nat) := ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1) -> ~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1).
Definition term11 := imp (forall y0 : nat, forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)).
Definition term118 (x0 : nat) (x1 : nat) := (((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = (Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0))) /\ (~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1))) -> ~ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1).
Definition term122 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term111 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x0 = x1)) \/ (x1 = x2)).
Definition term51 := fun y0 : nat => forall y1 : nat, ((y1 = (NUMERAL 0)) \/ (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)))) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term44 := fun y0 : nat => forall y1 : nat, (y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term30 := fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term24 := fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> (forall y2 : nat, forall y3 : nat, (Nat.mul y2 y3) = (Nat.mul y3 y2)) -> ~ (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)).
Definition term23 := fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (~ ((Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> (forall y2 : nat, forall y3 : nat, (Nat.mul y2 y3) = (Nat.mul y3 y2)) -> (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)) -> False.
Definition term101 (x0 : Prop) := x0 -> ~ x0.
Definition term126 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x0 = x2) /\ (~ (x1 = x2))).
Definition term119 (x0 : nat) (x1 : nat) := ~ ((Nat.add (Nat.mul (Nat.div x1 x0) x0) (Nat.modulo x1 x0)) = x1).
Definition term3 (x0 : nat) (x1 : nat) := ~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1).
