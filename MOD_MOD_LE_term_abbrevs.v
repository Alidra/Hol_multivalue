Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term90 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1).
Definition term109 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.lt (Nat.modulo x0 x1) x1) \/ (x1 = (NUMERAL 0))).
Definition term104 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term139 := (~ False) -> False.
Definition term98 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 y0))) \/ (Peano.lt x1 y0)) x2.
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) := or (~ ((Peano.lt x0 x1) /\ (Peano.le x1 x2))).
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x1) /\ (Peano.le x1 x2).
Definition term128 (x0 : Prop) := ~ (~ x0).
Definition term140 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y1 = (NUMERAL 0))) -> (Peano.le y1 y0) -> (~ (Peano.lt (Nat.modulo y2 y1) y0)) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.lt y3 y4) /\ (Peano.le y4 y5)) -> Peano.lt y3 y5) -> (forall y3 : nat, forall y4 : nat, (~ (y4 = (NUMERAL 0))) -> (y3 = (Nat.add (Nat.mul (Nat.div y3 y4) y4) (Nat.modulo y3 y4))) /\ (Peano.lt (Nat.modulo y3 y4) y4)) -> False) x0.
Definition term96 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y2))) \/ (Peano.lt y0 y2)) x0.
Definition term12 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0) -> (Nat.modulo x1 x0) = x1.
Definition term86 (x0 : nat) := forall y0 : nat, (y0 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term118 (x0 : nat) (x1 : nat) := or (~ (Peano.lt x0 x1)).
Definition term127 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (Peano.lt x0 x1))) /\ (~ (~ (Peano.le x1 x2))).
Definition term15 := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0) -> forall y0 : nat, forall y1 : nat, (Peano.lt y1 y0) -> (Nat.modulo y1 y0) = y1.
Definition term10 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) -> (Nat.modulo x0 y0) = x0) x1.
Definition term92 (x0 : nat) := fun y0 : nat => ((y0 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)))) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt (Nat.modulo x0 x1) x2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term21 (x0 : Prop) := (~ x0) -> False.
Definition term137 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt (Nat.modulo x0 x1) x2)) -> Peano.lt (Nat.modulo x0 x1) x2.
Definition term93 (x0 : nat) := forall y0 : nat, ((y0 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)))) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term133 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (Peano.lt x0 x1)) \/ (~ (Peano.le x1 x2)))).
Definition term74 (x0 : nat) (x1 : nat) := forall y0 : nat, ((~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 y0))) \/ (Peano.lt x1 y0).
Definition term142 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (x0 = (NUMERAL 0))) -> (Peano.le x0 x1) -> (~ (Peano.lt (Nat.modulo y0 x0) x1)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.le y2 y3)) -> Peano.lt y1 y3) -> (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)) -> False) x2.
Definition term113 (x0 : nat) (x1 : nat) := ~ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term123 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 x2)))) -> Peano.lt x1 x2.
Definition term111 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> Peano.lt (Nat.modulo x0 x1) x1.
Definition term110 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term108 (x0 : nat) (x1 : nat) := @eq Prop ((x1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (Peano.lt (Nat.modulo x0 x1) x2).
Definition term30 := ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term80 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term38 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term114 (x0 : Prop) := (~ x0) -> x0.
Definition term100 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((y0 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)))) /\ ((y0 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 y0) y0))) x1.
Definition term85 (x0 : nat) := fun y0 : nat => (y0 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)).
Definition term41 (x0 : nat) := imp (~ (x0 = (NUMERAL 0))).
Definition term125 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term121 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (Peano.lt x1 x0)) \/ ((~ (Peano.le x0 x2)) \/ (Peano.lt x1 x2))).
Definition term115 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> Peano.le x0 x1.
Definition term122 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Peano.lt x0 x2) \/ ((~ (Peano.lt x0 x1)) \/ (~ (Peano.le x1 x2)))).
Definition term120 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x2) \/ ((~ (Peano.lt x0 x1)) \/ (~ (Peano.le x1 x2))).
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = (NUMERAL 0))) -> (Peano.le x1 x2) -> (~ (Peano.lt (Nat.modulo x0 x1) x2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term33 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term138 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt (Nat.modulo x0 x1) x2) -> False.
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term141 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le y0 x0) -> (~ (Peano.lt (Nat.modulo y1 y0) x0)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.lt y2 y3) /\ (Peano.le y3 y4)) -> Peano.lt y2 y4) -> (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)) -> False) x1.
Definition term97 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 y1))) \/ (Peano.lt x0 y1)) x1.
Definition term19 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term75 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 y1))) \/ (Peano.lt x0 y1).
Definition term62 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.le y0 y1)) -> Peano.lt x0 y1.
Definition term83 (x0 : nat) (x1 : nat) := (~ (~ (x1 = (NUMERAL 0)))) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term129 (x0 : nat) (x1 : nat) := ~ (~ (Peano.lt x0 x1)).
Definition term117 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x2) \/ (~ (Peano.le x1 x2)).
Definition term103 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term101 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt x1 x0)) \/ ((~ (Peano.le x0 x2)) \/ (Peano.lt x1 x2)).
Definition term29 := (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term46 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le x0 x1) -> (~ (Peano.lt (Nat.modulo y0 x0) x1)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.le y2 y3)) -> Peano.lt y1 y3) -> ~ (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)).
Definition term45 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (x0 = (NUMERAL 0))) -> (Peano.le x0 x1) -> (~ (Peano.lt (Nat.modulo y0 x0) x1)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.le y2 y3)) -> Peano.lt y1 y3) -> (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)) -> False.
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) := (((~ (x1 = (NUMERAL 0))) -> (Peano.le x1 x2) -> (~ (Peano.lt (Nat.modulo x0 x1) x2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x1 = (NUMERAL 0))) -> (Peano.le x1 x2) -> (~ (Peano.lt (Nat.modulo x0 x1) x2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> ((~ (x1 = (NUMERAL 0))) -> (Peano.le x1 x2) -> (~ (Peano.lt (Nat.modulo x0 x1) x2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x1 = (NUMERAL 0))) -> (Peano.le x1 x2) -> (~ (Peano.lt (Nat.modulo x0 x1) x2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term81 (x0 : nat) := or (~ (~ (x0 = (NUMERAL 0)))).
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 x2))) \/ (Peano.lt x1 x2).
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 x2) -> (~ (Peano.lt (Nat.modulo x0 x1) x2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term56 (x0 : nat) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term82 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term124 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term147 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (y1 = (NUMERAL 0))) /\ (Peano.le y1 y2)) -> (Nat.modulo (Nat.modulo y0 y1) y2) = (Nat.modulo y0 y1).
Definition term146 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((~ (y0 = (NUMERAL 0))) /\ (Peano.le y0 y1)) -> (Nat.modulo (Nat.modulo x0 y0) y1) = (Nat.modulo x0 y0).
Definition term95 := forall y0 : nat, forall y1 : nat, ((y1 = (NUMERAL 0)) \/ (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)))) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term88 := forall y0 : nat, forall y1 : nat, (y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term78 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y2))) \/ (Peano.lt y0 y2).
Definition term76 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 y1))) \/ (Peano.lt x0 y1).
Definition term65 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2.
Definition term63 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.le y0 y1)) -> Peano.lt x0 y1.
Definition term54 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y1 = (NUMERAL 0))) -> (Peano.le y1 y0) -> (~ (Peano.lt (Nat.modulo y2 y1) y0)) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.lt y3 y4) /\ (Peano.le y4 y5)) -> Peano.lt y3 y5) -> ~ (forall y3 : nat, forall y4 : nat, (~ (y4 = (NUMERAL 0))) -> (y3 = (Nat.add (Nat.mul (Nat.div y3 y4) y4) (Nat.modulo y3 y4))) /\ (Peano.lt (Nat.modulo y3 y4) y4)).
Definition term53 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (~ (y1 = (NUMERAL 0))) -> (Peano.le y1 y0) -> (~ (Peano.lt (Nat.modulo y2 y1) y0)) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.lt y3 y4) /\ (Peano.le y4 y5)) -> Peano.lt y3 y5) -> (forall y3 : nat, forall y4 : nat, (~ (y4 = (NUMERAL 0))) -> (y3 = (Nat.add (Nat.mul (Nat.div y3 y4) y4) (Nat.modulo y3 y4))) /\ (Peano.lt (Nat.modulo y3 y4) y4)) -> False.
Definition term50 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le y0 x0) -> (~ (Peano.lt (Nat.modulo y1 y0) x0)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.lt y2 y3) /\ (Peano.le y3 y4)) -> Peano.lt y2 y4) -> ~ (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)).
Definition term49 (x0 : nat) := forall y0 : nat, forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le y0 x0) -> (~ (Peano.lt (Nat.modulo y1 y0) x0)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.lt y2 y3) /\ (Peano.le y3 y4)) -> Peano.lt y2 y4) -> (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)) -> False.
Definition term31 := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term14 := forall y0 : nat, forall y1 : nat, (Peano.lt y1 y0) -> (Nat.modulo y1 y0) = y1.
Definition term7 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0.
Definition term17 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt y0 x0) -> (Nat.modulo y0 x0) = y0) x1.
Definition term107 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.modulo x0 x1) x1) \/ (x1 = (NUMERAL 0)).
Definition term55 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term73 (x0 : nat) (x1 : nat) := fun y0 : nat => ((~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 y0))) \/ (Peano.lt x1 y0).
Definition term144 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (x2 = (NUMERAL 0))) /\ (Peano.le x2 x0)) -> (Nat.modulo (Nat.modulo x1 x2) x0) = (Nat.modulo x1 x2).
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.modulo x0 x1) x2.
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ (Peano.lt (Nat.modulo x0 x1) x2)).
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (x1 = (NUMERAL 0))) -> (Peano.le x1 x2) -> (~ (Peano.lt (Nat.modulo x0 x1) x2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x1 = (NUMERAL 0))) -> (Peano.le x1 x2) -> (~ (Peano.lt (Nat.modulo x0 x1) x2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term136 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt (Nat.modulo x0 x1) x1) /\ (Peano.le x1 x2)) -> Peano.lt (Nat.modulo x0 x1) x2.
Definition term135 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt (Nat.modulo x0 x1) x1) /\ (Peano.le x1 x2).
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) := or ((~ (Peano.lt x0 x1)) \/ (~ (Peano.le x1 x2))).
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = (NUMERAL 0))) -> (Peano.le x1 x2) -> (~ (Peano.lt (Nat.modulo x0 x1) x2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term105 (x0 : nat) := (x0 = (NUMERAL 0)) -> ~ (x0 = (NUMERAL 0)).
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x1 x2) -> (~ (Peano.lt (Nat.modulo x0 x1) x2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term131 (x0 : nat) (x1 : nat) := and (Peano.lt x0 x1).
Definition term134 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Peano.lt x0 x1) /\ (Peano.le x1 x2)).
Definition term11 (x0 : nat) (x1 : nat) := (Peano.lt x1 x0) -> (Nat.modulo x1 x0) = x1.
Definition term130 (x0 : nat) (x1 : nat) := and (~ (~ (Peano.lt x0 x1))).
Definition term44 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (x0 = (NUMERAL 0))) -> (Peano.le x0 x1) -> (~ (Peano.lt (Nat.modulo y0 x0) x1)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.le y2 y3)) -> Peano.lt y1 y3) -> ~ (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)).
Definition term43 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (x0 = (NUMERAL 0))) -> (Peano.le x0 x1) -> (~ (Peano.lt (Nat.modulo y0 x0) x1)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.le y2 y3)) -> Peano.lt y1 y3) -> (forall y1 : nat, forall y2 : nat, (~ (y2 = (NUMERAL 0))) -> (y1 = (Nat.add (Nat.mul (Nat.div y1 y2) y2) (Nat.modulo y1 y2))) /\ (Peano.lt (Nat.modulo y1 y2) y2)) -> False.
Definition term61 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.lt x1 x0) /\ (Peano.le x0 y0)) -> Peano.lt x1 y0.
Definition term143 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.modulo x0 x1) x2.
Definition term18 (x0 : nat) (x1 : nat) := (~ (x0 = (NUMERAL 0))) /\ (Peano.le x0 x1).
Definition term102 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term99 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((y1 = (NUMERAL 0)) \/ (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)))) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo y0 y1) y1))) x0.
Definition term16 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) -> (Nat.modulo y1 y0) = y1) x0.
Definition term8 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0) x0.
Definition term132 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term145 (x0 : nat) (x1 : nat) := forall y0 : nat, ((~ (x1 = (NUMERAL 0))) /\ (Peano.le x1 y0)) -> (Nat.modulo (Nat.modulo x0 x1) y0) = (Nat.modulo x0 x1).
Definition term13 (x0 : nat) := forall y0 : nat, (Peano.lt y0 x0) -> (Nat.modulo y0 x0) = y0.
Definition term66 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Peano.lt x0 x1) /\ (Peano.le x1 x2)).
Definition term89 (x0 : nat) (x1 : nat) := ((x1 = (NUMERAL 0)) \/ (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)))) /\ ((x1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term59 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt x1 x0) /\ (Peano.le x0 x2)) -> Peano.lt x1 x2.
Definition term126 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (Peano.lt x0 x1)) \/ (~ (Peano.le x1 x2))).
Definition term34 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := (((~ (x1 = (NUMERAL 0))) -> (Peano.le x1 x2) -> (~ (Peano.lt (Nat.modulo x0 x1) x2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x1 = (NUMERAL 0))) -> (Peano.le x1 x2) -> (~ (Peano.lt (Nat.modulo x0 x1) x2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False) -> (~ (x1 = (NUMERAL 0))) -> (Peano.le x1 x2) -> (~ (Peano.lt (Nat.modulo x0 x1) x2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> False.
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt x0 x1)) \/ (~ (Peano.le x1 x2)).
Definition term91 (x0 : nat) (x1 : nat) := Peano.lt (Nat.modulo x0 x1) x1.
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt (Nat.modulo x0 x1) x2)) -> False.
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt (Nat.modulo x1 x2) x0) -> (Nat.modulo (Nat.modulo x1 x2) x0) = (Nat.modulo x1 x2).
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt (Nat.modulo x0 x1) x2)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> ~ (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term84 (x0 : nat) (x1 : nat) := (x1 = (NUMERAL 0)) \/ ((x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1)).
Definition term119 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt x0 x1)) \/ ((Peano.lt x0 x2) \/ (~ (Peano.le x1 x2))).
Definition term116 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x2)) \/ (Peano.lt x1 x2).
Definition term79 (x0 : nat) := ~ (~ (x0 = (NUMERAL 0))).
Definition term57 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term32 := imp (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2).
Definition term94 := fun y0 : nat => forall y1 : nat, ((y1 = (NUMERAL 0)) \/ (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)))) /\ ((y1 = (NUMERAL 0)) \/ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term87 := fun y0 : nat => forall y1 : nat, (y1 = (NUMERAL 0)) \/ ((y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)).
Definition term58 := fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term48 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le y0 x0) -> (~ (Peano.lt (Nat.modulo y1 y0) x0)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.lt y2 y3) /\ (Peano.le y3 y4)) -> Peano.lt y2 y4) -> ~ (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)).
Definition term47 (x0 : nat) := fun y0 : nat => forall y1 : nat, (~ (y0 = (NUMERAL 0))) -> (Peano.le y0 x0) -> (~ (Peano.lt (Nat.modulo y1 y0) x0)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.lt y2 y3) /\ (Peano.le y3 y4)) -> Peano.lt y2 y4) -> (forall y2 : nat, forall y3 : nat, (~ (y3 = (NUMERAL 0))) -> (y2 = (Nat.add (Nat.mul (Nat.div y2 y3) y3) (Nat.modulo y2 y3))) /\ (Peano.lt (Nat.modulo y2 y3) y3)) -> False.
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Peano.lt x1 x0) /\ (Peano.le x0 x2))) \/ (Peano.lt x1 x2).
Definition term60 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Peano.lt x1 x0) /\ (Peano.le x0 y0)) -> Peano.lt x1 y0.
Definition term106 (x0 : Prop) := x0 -> ~ x0.
Definition term77 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y2))) \/ (Peano.lt y0 y2).
Definition term64 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2.
Definition term52 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y1 = (NUMERAL 0))) -> (Peano.le y1 y0) -> (~ (Peano.lt (Nat.modulo y2 y1) y0)) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.lt y3 y4) /\ (Peano.le y4 y5)) -> Peano.lt y3 y5) -> ~ (forall y3 : nat, forall y4 : nat, (~ (y4 = (NUMERAL 0))) -> (y3 = (Nat.add (Nat.mul (Nat.div y3 y4) y4) (Nat.modulo y3 y4))) /\ (Peano.lt (Nat.modulo y3 y4) y4)).
Definition term51 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (~ (y1 = (NUMERAL 0))) -> (Peano.le y1 y0) -> (~ (Peano.lt (Nat.modulo y2 y1) y0)) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.lt y3 y4) /\ (Peano.le y4 y5)) -> Peano.lt y3 y5) -> (forall y3 : nat, forall y4 : nat, (~ (y4 = (NUMERAL 0))) -> (y3 = (Nat.add (Nat.mul (Nat.div y3 y4) y4) (Nat.modulo y3 y4))) /\ (Peano.lt (Nat.modulo y3 y4) y4)) -> False.
Definition term112 (x0 : nat) (x1 : nat) := (~ (Peano.lt (Nat.modulo x0 x1) x1)) -> Peano.lt (Nat.modulo x0 x1) x1.
Definition term9 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) -> (Nat.modulo x0 y0) = x0.
