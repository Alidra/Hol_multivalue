Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term93 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul (Nat.add x0 x1) x2).
Definition term171 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 (NUMERAL 0)) x1.
Definition term205 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((fun y0 : nat => x0 = (Nat.add (Nat.mul x1 x2) y0)) x3).
Definition term200 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((fun y0 : nat => (x0 = x1) /\ (y0 = x2)) x3).
Definition term225 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (x0 = (Nat.add (Nat.mul x4 x1) x2)) -> x3 = x4.
Definition term196 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (x0 = x1) /\ (y0 = x2).
Definition term95 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul (Nat.add x0 x1) x2) x3.
Definition term42 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0))) x1.
Definition term140 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.lt (Nat.add (Nat.mul x0 y1) x1) x0) -> (Nat.add (Nat.mul x0 y1) x1) = x1) y0.
Definition term222 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.add x0 y0) = (Nat.add x1 y0)) = (x0 = x1).
Definition term203 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => x0 = (Nat.add (Nat.mul x1 x2) y0).
Definition term242 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := (((x0 = (Nat.add (Nat.mul x2 x1) x4)) /\ (Peano.lt x4 x1)) /\ ((x0 = (Nat.add (Nat.mul x3 x1) x5)) /\ (Peano.lt x5 x1))) -> (x2 = x3) /\ (x4 = x5).
Definition term2 (x0 : nat) := fun y0 : nat => (Peano.lt y0 x0) = (~ (Peano.le x0 y0)).
Definition term4 (x0 : nat) := forall y0 : nat, (Peano.lt y0 x0) = (~ (Peano.le x0 y0)).
Definition term90 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (fun y0 : nat => ((Nat.add (Nat.mul y0 x0) x1) = (Nat.add (Nat.mul x3 x0) x2)) -> x1 = x2) (Nat.add x3 x4).
Definition term84 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (fun y0 : nat => ((Nat.add (Nat.mul x3 x0) x1) = (Nat.add (Nat.mul y0 x0) x2)) -> x1 = x2) (Nat.add x3 x4).
Definition term120 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> (Nat.add (Nat.mul x0 y0) x1) = x1.
Definition term230 := @eq nat (NUMERAL 0).
Definition term201 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = x1) /\ (x2 = x3).
Definition term36 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term219 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y2) = (Nat.add y1 y2)) = (y0 = y1)) x0.
Definition term213 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y2) = (Nat.mul y1 y2)) = ((y0 = y1) \/ (y2 = (NUMERAL 0)))) x0.
Definition term59 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.mul (Nat.add y0 y1) y2) = (Nat.add (Nat.mul y0 y2) (Nat.mul y1 y2))) x0.
Definition term54 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y1) = (Nat.add y0 y2)) = (y1 = y2)) x0.
Definition term26 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2))) x0.
Definition term121 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> (Nat.add (Nat.mul x0 y0) x1) = x1) (NUMERAL 0).
Definition term1 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term240 (x0 : nat) (x1 : nat) := (x0 = x1) -> x0 = x1.
Definition term127 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Peano.lt (Nat.add (Nat.mul x0 x1) x2) x0) -> (Nat.add (Nat.mul x0 x1) x2) = x2).
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : nat) := ((x2 = (Nat.add (Nat.mul x0 x5) x1)) /\ (Peano.lt x1 x5)) /\ ((x2 = (Nat.add (Nat.mul x3 x5) x4)) /\ (Peano.lt x4 x5)).
Definition term102 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := imp ((Nat.add (Nat.mul (Nat.add x2 x0) x3) x1) = (Nat.add (Nat.mul x2 x3) x4)).
Definition term79 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := imp ((Nat.add (Nat.mul x0 x3) x1) = (Nat.add (Nat.mul x2 x3) x4)).
Definition term224 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x0 = x1) \/ (x2 = (NUMERAL 0))).
Definition term223 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.add x0 y0) = (Nat.add x1 y0)) = (x0 = x1)) x2.
Definition term193 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.add x1 y0).
Definition term122 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.add (Nat.mul x0 (NUMERAL 0)) x1) x0) -> (Nat.add (Nat.mul x0 (NUMERAL 0)) x1) = x1.
Definition term241 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x2 = x3) -> (x0 = x1) /\ (x2 = x3).
Definition term104 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.add (Nat.mul x0 x1) x2) = x3) -> x2 = x3.
Definition term41 (x0 : nat) := forall y0 : nat, (Nat.mul x0 (S y0)) = (Nat.add x0 (Nat.mul x0 y0)).
Definition term113 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 x1).
Definition term181 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 (S x1)) x2.
Definition term38 := (forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))).
Definition term172 (x0 : nat) := Nat.add (Nat.mul x0 (NUMERAL 0)).
Definition term146 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y0) x1)) (NUMERAL 0).
Definition term236 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x1) -> (Peano.lt x0 x1) -> ((x2 = x3) \/ (x1 = (NUMERAL 0))) -> x2 = x3.
Definition term57 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.add x0 x1) = (Nat.add x0 y0)) = (x1 = y0).
Definition term235 (x0 : nat) (x1 : nat) := False -> x0 = x1.
Definition term187 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le x0 (Nat.add x0 (Nat.add (Nat.mul x0 x1) x2)).
Definition term166 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.lt (Nat.add (Nat.mul x0 y1) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y1) x1)) y0.
Definition term141 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.lt (Nat.add (Nat.mul x0 y1) x1) x0) -> (Nat.add (Nat.mul x0 y1) x1) = x1) y0.
Definition term98 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := imp ((Nat.add (Nat.mul x1 x3) x0) = (Nat.add (Nat.mul (Nat.add x1 x2) x3) x4)).
Definition term72 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) \/ (Peano.le y0 x0)) x1.
Definition term131 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt (Nat.add (Nat.mul x0 x1) x2) x0) -> (Nat.add (Nat.mul x0 x1) x2) = x2) -> (Peano.lt (Nat.add (Nat.mul x0 (S x1)) x2) x0) -> (Nat.add (Nat.mul x0 (S x1)) x2) = x2.
Definition term161 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y0) x1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.lt (Nat.add (Nat.mul x0 y1) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y1) x1)) y0) -> (fun y1 : nat => (Peano.lt (Nat.add (Nat.mul x0 y1) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y1) x1)) (S y0)).
Definition term136 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> (Nat.add (Nat.mul x0 y0) x1) = x1) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.lt (Nat.add (Nat.mul x0 y1) x1) x0) -> (Nat.add (Nat.mul x0 y1) x1) = x1) y0) -> (fun y1 : nat => (Peano.lt (Nat.add (Nat.mul x0 y1) x1) x0) -> (Nat.add (Nat.mul x0 y1) x1) = x1) (S y0)).
Definition term67 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term211 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term129 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt (Nat.add (Nat.mul x0 (S x1)) x2) x0) -> (Nat.add (Nat.mul x0 (S x1)) x2) = x2.
Definition term116 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt (Nat.add (Nat.mul x0 x1) x2) x0) -> (Nat.add (Nat.mul x0 x1) x2) = x2.
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term227 (x0 : nat) := (fun y0 : nat => Peano.le (NUMERAL 0) y0) x0.
Definition term189 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.add (Nat.mul x0 (S x1)) x2).
Definition term185 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add (Nat.mul x0 x1) x2).
Definition term110 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt (Nat.add (Nat.mul x0 x1) x2) x1) -> (Nat.add (Nat.mul x0 x1) x2) = x2.
Definition term144 (x0 : nat) (x1 : nat) := (((fun y0 : nat => (Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y0) x1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.lt (Nat.add (Nat.mul x0 y1) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y1) x1)) y0) -> (fun y1 : nat => (Peano.lt (Nat.add (Nat.mul x0 y1) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y1) x1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => (Peano.lt (Nat.add (Nat.mul x0 y1) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y1) x1)) y0.
Definition term119 (x0 : nat) (x1 : nat) := (((fun y0 : nat => (Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> (Nat.add (Nat.mul x0 y0) x1) = x1) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.lt (Nat.add (Nat.mul x0 y1) x1) x0) -> (Nat.add (Nat.mul x0 y1) x1) = x1) y0) -> (fun y1 : nat => (Peano.lt (Nat.add (Nat.mul x0 y1) x1) x0) -> (Nat.add (Nat.mul x0 y1) x1) = x1) (S y0))) -> forall y0 : nat, (fun y1 : nat => (Peano.lt (Nat.add (Nat.mul x0 y1) x1) x0) -> (Nat.add (Nat.mul x0 y1) x1) = x1) y0.
Definition term194 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (Peano.le x1 x0) -> ((Nat.add (Nat.mul x0 x2) x3) = (Nat.add (Nat.mul x1 x2) x4)) -> x3 = x4.
Definition term14 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term133 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> (Nat.add (Nat.mul x0 y0) x1) = x1) -> (Peano.lt (Nat.add (Nat.mul x0 (S y0)) x1) x0) -> (Nat.add (Nat.mul x0 (S y0)) x1) = x1.
Definition term158 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y0) x1)) -> (Peano.lt (Nat.add (Nat.mul x0 (S y0)) x1) x0) -> x1 = (Nat.add (Nat.mul x0 (S y0)) x1).
Definition term30 (x0 : nat) := forall y0 : nat, Peano.le x0 (Nat.add x0 y0).
Definition term118 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term75 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3).
Definition term142 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> (Nat.add (Nat.mul x0 y0) x1) = x1.
Definition term163 (x0 : nat) (x1 : nat) := imp (((fun y0 : nat => (Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y0) x1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.lt (Nat.add (Nat.mul x0 y1) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y1) x1)) y0) -> (fun y1 : nat => (Peano.lt (Nat.add (Nat.mul x0 y1) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y1) x1)) (S y0))).
Definition term138 (x0 : nat) (x1 : nat) := imp (((fun y0 : nat => (Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> (Nat.add (Nat.mul x0 y0) x1) = x1) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Peano.lt (Nat.add (Nat.mul x0 y1) x1) x0) -> (Nat.add (Nat.mul x0 y1) x1) = x1) y0) -> (fun y1 : nat => (Peano.lt (Nat.add (Nat.mul x0 y1) x1) x0) -> (Nat.add (Nat.mul x0 y1) x1) = x1) (S y0))).
Definition term16 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term150 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y0) x1)) x2.
Definition term153 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y0) x1)) (S x2).
Definition term218 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x1) \/ (x2 = (NUMERAL 0)).
Definition term100 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq nat (Nat.add (Nat.mul (Nat.add x0 x1) x2) x3).
Definition term216 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.mul x0 y0) = (Nat.mul x1 y0)) = ((x0 = x1) \/ (y0 = (NUMERAL 0))).
Definition term221 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add x0 y1) = (Nat.add y0 y1)) = (x0 = y0)) x1.
Definition term215 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.mul x0 y1) = (Nat.mul y0 y1)) = ((x0 = y0) \/ (y1 = (NUMERAL 0)))) x1.
Definition term61 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1))) x1.
Definition term56 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1)) x1.
Definition term27 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1))) x1.
Definition term192 (x0 : nat) (x1 : nat) (x2 : nat) := False -> x2 = (Nat.add x0 (Nat.add (Nat.mul x0 x1) x2)).
Definition term159 (x0 : nat) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => (Peano.lt (Nat.add (Nat.mul x0 y1) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y1) x1)) y0) -> (fun y1 : nat => (Peano.lt (Nat.add (Nat.mul x0 y1) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y1) x1)) (S y0).
Definition term134 (x0 : nat) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => (Peano.lt (Nat.add (Nat.mul x0 y1) x1) x0) -> (Nat.add (Nat.mul x0 y1) x1) = x1) y0) -> (fun y1 : nat => (Peano.lt (Nat.add (Nat.mul x0 y1) x1) x0) -> (Nat.add (Nat.mul x0 y1) x1) = x1) (S y0).
Definition term11 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term18 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term5 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term43 (x0 : nat) (x1 : nat) := Nat.mul x0 (S x1).
Definition term71 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) \/ (Peano.le y0 x0).
Definition term124 (x0 : nat) (x1 : nat) := and ((Peano.lt (Nat.add (Nat.mul x0 (NUMERAL 0)) x1) x0) -> (Nat.add (Nat.mul x0 (NUMERAL 0)) x1) = x1).
Definition term31 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le x0 (Nat.add x0 y0)) x1.
Definition term96 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.add (Nat.mul x0 x2) (Nat.mul x1 x2)) x3.
Definition term175 (x0 : nat) (x1 : nat) := imp (Peano.lt (Nat.add (Nat.mul x1 (NUMERAL 0)) x0) x1).
Definition term179 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.add (Nat.mul x2 (S x0)) x1) x2.
Definition term148 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y0) x1)) (NUMERAL 0)).
Definition term123 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> (Nat.add (Nat.mul x0 y0) x1) = x1) (NUMERAL 0)).
Definition term0 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term46 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) x0.
Definition term91 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := ((Nat.add (Nat.mul (Nat.add x1 x0) x2) x3) = (Nat.add (Nat.mul x1 x2) x4)) -> x3 = x4.
Definition term85 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := ((Nat.add (Nat.mul x0 x2) x3) = (Nat.add (Nat.mul (Nat.add x0 x1) x2) x4)) -> x3 = x4.
Definition term81 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := ((Nat.add (Nat.mul x0 x2) x3) = (Nat.add (Nat.mul x1 x2) x4)) -> x3 = x4.
Definition term197 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => (x0 = x1) /\ (y0 = x2)) x3.
Definition term78 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp (x0 = (Nat.add (Nat.mul x1 x2) x3)).
Definition term177 (x0 : nat) (x1 : nat) := @eq nat (Nat.add (Nat.mul x0 (NUMERAL 0)) x1).
Definition term125 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> (Nat.add (Nat.mul x0 y0) x1) = x1) x2.
Definition term210 (x0 : nat) (x1 : nat) := @eq Prop (Peano.lt x0 x1).
Definition term207 (x0 : nat) := fun y0 : nat => Peano.lt y0 x0.
Definition term157 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (Peano.lt (Nat.add (Nat.mul x0 y1) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y1) x1)) y0) -> (fun y1 : nat => (Peano.lt (Nat.add (Nat.mul x0 y1) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y1) x1)) (S y0).
Definition term132 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (Peano.lt (Nat.add (Nat.mul x0 y1) x1) x0) -> (Nat.add (Nat.mul x0 y1) x1) = x1) y0) -> (fun y1 : nat => (Peano.lt (Nat.add (Nat.mul x0 y1) x1) x0) -> (Nat.add (Nat.mul x0 y1) x1) = x1) (S y0).
Definition term178 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> True.
Definition term170 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 (Nat.add (Nat.mul x0 (NUMERAL 0)) x1)).
Definition term239 (x0 : nat) (x1 : nat) := imp (x0 = x1).
Definition term69 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 y0).
Definition term165 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.lt (Nat.add (Nat.mul x0 y1) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y1) x1)) y0.
Definition term50 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term217 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.mul x0 y0) = (Nat.mul x1 y0)) = ((x0 = x1) \/ (y0 = (NUMERAL 0)))) x2.
Definition term248 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, forall y5 : nat, (((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) /\ ((y0 = (Nat.add (Nat.mul y4 y1) y5)) /\ (Peano.lt y5 y1))) -> (y2 = y4) /\ (y3 = y5).
Definition term247 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, forall y4 : nat, (((x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) /\ ((x0 = (Nat.add (Nat.mul y3 y0) y4)) /\ (Peano.lt y4 y0))) -> (y1 = y3) /\ (y2 = y4).
Definition term246 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, (((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) /\ ((x0 = (Nat.add (Nat.mul y2 x1) y3)) /\ (Peano.lt y3 x1))) -> (y0 = y2) /\ (y1 = y3).
Definition term245 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, (((x0 = (Nat.add (Nat.mul x2 x1) y0)) /\ (Peano.lt y0 x1)) /\ ((x0 = (Nat.add (Nat.mul y1 x1) y2)) /\ (Peano.lt y2 x1))) -> (x2 = y1) /\ (y0 = y2).
Definition term244 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := forall y0 : nat, forall y1 : nat, (((x0 = (Nat.add (Nat.mul x2 x1) x3)) /\ (Peano.lt x3 x1)) /\ ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1))) -> (x2 = y0) /\ (x3 = y1).
Definition term220 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.add x0 y1) = (Nat.add y0 y1)) = (x0 = y0).
Definition term214 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.mul x0 y1) = (Nat.mul y0 y1)) = ((x0 = y0) \/ (y1 = (NUMERAL 0))).
Definition term60 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.mul (Nat.add x0 y0) y1) = (Nat.add (Nat.mul x0 y1) (Nat.mul y0 y1)).
Definition term55 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.add x0 y0) = (Nat.add x0 y1)) = (y0 = y1).
Definition term39 := forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)).
Definition term25 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2)).
Definition term24 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2).
Definition term21 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1)).
Definition term20 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term8 := forall y0 : nat, forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1)).
Definition term7 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term169 (x0 : nat) (x1 : nat) := Peano.lt (Nat.add (Nat.mul x1 (NUMERAL 0)) x0) x1.
Definition term10 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term3 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term209 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => Peano.lt y0 x0) x1).
Definition term103 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((Nat.add (Nat.mul x0 x1) x2) = x3).
Definition term77 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.add (Nat.mul x0 x1) x2).
Definition term63 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0))) x2.
Definition term208 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.lt y0 x0) x1.
Definition term168 (x0 : nat) (x1 : nat) := (((Peano.lt (Nat.add (Nat.mul x0 (NUMERAL 0)) x1) x0) -> x1 = (Nat.add (Nat.mul x0 (NUMERAL 0)) x1)) /\ (forall y0 : nat, ((Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y0) x1)) -> (Peano.lt (Nat.add (Nat.mul x0 (S y0)) x1) x0) -> x1 = (Nat.add (Nat.mul x0 (S y0)) x1))) -> forall y0 : nat, (Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y0) x1).
Definition term92 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := @eq Prop ((fun y0 : nat => ((Nat.add (Nat.mul y0 x1) x2) = (Nat.add (Nat.mul x0 x1) x3)) -> x2 = x3) x4).
Definition term86 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := @eq Prop ((fun y0 : nat => ((Nat.add (Nat.mul x0 x1) x2) = (Nat.add (Nat.mul y0 x1) x3)) -> x2 = x3) x4).
Definition term99 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x2 = (Nat.add (Nat.mul x0 x1) x3)) -> x2 = x3.
Definition term198 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (x0 = x1) /\ (y0 = x2)) x2.
Definition term48 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term191 (x0 : nat) (x1 : nat) (x2 : nat) := False -> (Nat.add x0 (Nat.add (Nat.mul x0 x1) x2)) = x2.
Definition term206 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop (x0 = (Nat.add (Nat.mul x1 x2) x3)).
Definition term145 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y0) x1).
Definition term49 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term87 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := @eq Prop (((Nat.add (Nat.mul x0 x2) x3) = (Nat.add (Nat.mul x1 x2) x4)) -> x3 = x4).
Definition term105 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.add (Nat.mul x0 x1) x2).
Definition term228 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term233 (x0 : nat) (x1 : nat) := True -> x0 = x1.
Definition term64 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.add x0 x1) x2.
Definition term65 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term186 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le x0 (Nat.add (Nat.mul x0 (S x1)) x2).
Definition term80 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (x0 = (Nat.add (Nat.mul x1 x2) x4)) -> x3 = x4.
Definition term143 (x0 : nat) (x1 : nat) := (((Peano.lt (Nat.add (Nat.mul x0 (NUMERAL 0)) x1) x0) -> (Nat.add (Nat.mul x0 (NUMERAL 0)) x1) = x1) /\ (forall y0 : nat, ((Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> (Nat.add (Nat.mul x0 y0) x1) = x1) -> (Peano.lt (Nat.add (Nat.mul x0 (S y0)) x1) x0) -> (Nat.add (Nat.mul x0 (S y0)) x1) = x1)) -> forall y0 : nat, (Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> (Nat.add (Nat.mul x0 y0) x1) = x1.
Definition term154 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt (Nat.add (Nat.mul x0 (S x1)) x2) x0) -> x2 = (Nat.add (Nat.mul x0 (S x1)) x2).
Definition term117 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt (Nat.add (Nat.mul x0 x1) x2) x0) -> x2 = (Nat.add (Nat.mul x0 x1) x2).
Definition term226 (x0 : nat) (x1 : nat) (x2 : nat) := ((x1 = x2) \/ (x0 = (NUMERAL 0))) -> x1 = x2.
Definition term128 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> (Nat.add (Nat.mul x0 y0) x1) = x1) (S x2).
Definition term73 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) \/ (Peano.le x0 x1).
Definition term52 (x0 : nat) := forall y0 : nat, (Nat.mul x0 y0) = (Nat.mul y0 x0).
Definition term139 (x0 : nat) (x1 : nat) := imp (((Peano.lt (Nat.add (Nat.mul x0 (NUMERAL 0)) x1) x0) -> (Nat.add (Nat.mul x0 (NUMERAL 0)) x1) = x1) /\ (forall y0 : nat, ((Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> (Nat.add (Nat.mul x0 y0) x1) = x1) -> (Peano.lt (Nat.add (Nat.mul x0 (S y0)) x1) x0) -> (Nat.add (Nat.mul x0 (S y0)) x1) = x1)).
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0))) x2.
Definition term149 (x0 : nat) (x1 : nat) := and ((Peano.lt (Nat.add (Nat.mul x0 (NUMERAL 0)) x1) x0) -> x1 = (Nat.add (Nat.mul x0 (NUMERAL 0)) x1)).
Definition term107 (x0 : nat) (x1 : nat) := imp (Peano.lt x0 x1).
Definition term101 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq nat (Nat.add (Nat.mul x0 x2) (Nat.add (Nat.mul x1 x2) x3)).
Definition term109 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x1 x0) -> x1 = x2.
Definition term53 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.mul x0 y0) = (Nat.mul y0 x0)) x1.
Definition term182 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x0 (S x1)).
Definition term37 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term137 (x0 : nat) (x1 : nat) := ((Peano.lt (Nat.add (Nat.mul x0 (NUMERAL 0)) x1) x0) -> (Nat.add (Nat.mul x0 (NUMERAL 0)) x1) = x1) /\ (forall y0 : nat, ((Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> (Nat.add (Nat.mul x0 y0) x1) = x1) -> (Peano.lt (Nat.add (Nat.mul x0 (S y0)) x1) x0) -> (Nat.add (Nat.mul x0 (S y0)) x1) = x1).
Definition term94 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add (Nat.mul x0 x2) (Nat.mul x1 x2)).
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term88 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := fun y0 : nat => ((Nat.add (Nat.mul y0 x1) x2) = (Nat.add (Nat.mul x0 x1) x3)) -> x2 = x3.
Definition term82 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := fun y0 : nat => ((Nat.add (Nat.mul x0 x1) x2) = (Nat.add (Nat.mul y0 x1) x3)) -> x2 = x3.
Definition term173 := Nat.add (NUMERAL 0).
Definition term180 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (Peano.le x0 (Nat.add (Nat.mul x0 (S x1)) x2)).
Definition term32 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.add x0 x1).
Definition term70 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) x0.
Definition term66 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) x0.
Definition term51 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 y1) = (Nat.mul y1 y0)) x0.
Definition term40 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))) x0.
Definition term33 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1))) x0.
Definition term29 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) x0.
Definition term45 := forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0).
Definition term188 (x0 : nat) (x1 : nat) (x2 : nat) := imp (Peano.lt (Nat.add (Nat.mul x2 (S x0)) x1) x2).
Definition term115 (x0 : nat) (x1 : nat) (x2 : nat) := imp (Peano.lt (Nat.add (Nat.mul x2 x0) x1) x2).
Definition term108 (x0 : nat) (x1 : nat) (x2 : nat) := imp (Peano.lt (Nat.add (Nat.mul x0 x2) x1) x2).
Definition term243 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := forall y0 : nat, (((x0 = (Nat.add (Nat.mul x2 x1) x4)) /\ (Peano.lt x4 x1)) /\ ((x0 = (Nat.add (Nat.mul x3 x1) y0)) /\ (Peano.lt y0 x1))) -> (x2 = x3) /\ (x4 = y0).
Definition term135 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> (Nat.add (Nat.mul x0 y0) x1) = x1) -> (Peano.lt (Nat.add (Nat.mul x0 (S y0)) x1) x0) -> (Nat.add (Nat.mul x0 (S y0)) x1) = x1.
Definition term152 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Peano.lt (Nat.add (Nat.mul x0 x1) x2) x0) -> x2 = (Nat.add (Nat.mul x0 x1) x2)).
Definition term204 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => x0 = (Nat.add (Nat.mul x1 x2) y0)) x3.
Definition term44 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.mul x0 x1).
Definition term47 (x0 : nat) := Nat.mul x0 (NUMERAL 0).
Definition term184 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 (Nat.mul x0 x1)) x2.
Definition term183 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x0 (Nat.mul x0 x1)).
Definition term62 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.mul (Nat.add x0 x1) y0) = (Nat.add (Nat.mul x0 y0) (Nat.mul x1 y0)).
Definition term176 (x0 : nat) (x1 : nat) := imp (~ (Peano.le x0 x1)).
Definition term111 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x2 x0) -> x1 = x2.
Definition term114 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.add (Nat.mul x2 x0) x1) x2.
Definition term106 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.add (Nat.mul x0 x2) x1) x2.
Definition term212 (x0 : nat) (x1 : nat) := (x0 = x1) /\ True.
Definition term34 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt y0 x0) = (~ (Peano.le x0 y0))) x1.
Definition term199 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x1) /\ (x2 = x2).
Definition term238 (x0 : nat) (x1 : nat) := (x0 = x1) \/ False.
Definition term237 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term156 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt (Nat.add (Nat.mul x0 x1) x2) x0) -> x2 = (Nat.add (Nat.mul x0 x1) x2)) -> (Peano.lt (Nat.add (Nat.mul x0 (S x1)) x2) x0) -> x2 = (Nat.add (Nat.mul x0 (S x1)) x2).
Definition term58 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.add x0 x1) = (Nat.add x0 y0)) = (x1 = y0)) x2.
Definition term164 (x0 : nat) (x1 : nat) := imp (((Peano.lt (Nat.add (Nat.mul x0 (NUMERAL 0)) x1) x0) -> x1 = (Nat.add (Nat.mul x0 (NUMERAL 0)) x1)) /\ (forall y0 : nat, ((Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y0) x1)) -> (Peano.lt (Nat.add (Nat.mul x0 (S y0)) x1) x0) -> x1 = (Nat.add (Nat.mul x0 (S y0)) x1))).
Definition term89 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (fun y0 : nat => ((Nat.add (Nat.mul y0 x1) x2) = (Nat.add (Nat.mul x0 x1) x3)) -> x2 = x3) x4.
Definition term83 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (fun y0 : nat => ((Nat.add (Nat.mul x0 x1) x2) = (Nat.add (Nat.mul y0 x1) x3)) -> x2 = x3) x4.
Definition term17 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0)).
Definition term6 := fun y0 : nat => forall y1 : nat, (Peano.lt y1 y0) = (~ (Peano.le y0 y1)).
Definition term97 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Nat.add (Nat.mul x0 x2) (Nat.add (Nat.mul x1 x2) x3).
Definition term229 := Peano.le (NUMERAL 0).
Definition term160 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y0) x1)) -> (Peano.lt (Nat.add (Nat.mul x0 (S y0)) x1) x0) -> x1 = (Nat.add (Nat.mul x0 (S y0)) x1).
Definition term155 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => (Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y0) x1)) x2) -> (fun y0 : nat => (Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y0) x1)) (S x2).
Definition term130 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => (Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> (Nat.add (Nat.mul x0 y0) x1) = x1) x2) -> (fun y0 : nat => (Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> (Nat.add (Nat.mul x0 y0) x1) = x1) (S x2).
Definition term162 (x0 : nat) (x1 : nat) := ((Peano.lt (Nat.add (Nat.mul x0 (NUMERAL 0)) x1) x0) -> x1 = (Nat.add (Nat.mul x0 (NUMERAL 0)) x1)) /\ (forall y0 : nat, ((Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y0) x1)) -> (Peano.lt (Nat.add (Nat.mul x0 (S y0)) x1) x0) -> x1 = (Nat.add (Nat.mul x0 (S y0)) x1)).
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x1) x2.
Definition term151 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((fun y0 : nat => (Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y0) x1)) x2).
Definition term126 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((fun y0 : nat => (Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> (Nat.add (Nat.mul x0 y0) x1) = x1) x2).
Definition term195 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (Peano.le x0 x1) -> ((Nat.add (Nat.mul x0 x2) x3) = (Nat.add (Nat.mul x1 x2) x4)) -> x3 = x4.
Definition term15 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add (Nat.add x0 x1) y0) = (Nat.add x0 (Nat.add x1 y0)).
Definition term147 (x0 : nat) (x1 : nat) := (Peano.lt (Nat.add (Nat.mul x0 (NUMERAL 0)) x1) x0) -> x1 = (Nat.add (Nat.mul x0 (NUMERAL 0)) x1).
Definition term68 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) x1.
Definition term234 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x1) -> ((x2 = x3) \/ (x1 = (NUMERAL 0))) -> x2 = x3.
Definition term174 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.add (Nat.mul x0 (NUMERAL 0)) x1).
Definition term35 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term190 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.add x0 (Nat.add (Nat.mul x0 x1) x2)).
Definition term232 (x0 : nat) (x1 : nat) := (x0 = x1) \/ True.
Definition term202 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((x0 = x1) /\ (x2 = x3)).
Definition term9 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term231 (x0 : nat) (x1 : nat) := or (x0 = x1).
Definition term19 (x0 : nat) := fun y0 : nat => forall y1 : nat, (Nat.add (Nat.add x0 y0) y1) = (Nat.add x0 (Nat.add y0 y1)).
Definition term23 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add (Nat.add y0 y1) y2) = (Nat.add y0 (Nat.add y1 y2)).
Definition term22 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2).
Definition term112 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt (Nat.add (Nat.mul x0 x1) x2) x1) -> x2 = (Nat.add (Nat.mul x0 x1) x2).
Definition term167 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.lt (Nat.add (Nat.mul x0 y0) x1) x0) -> x1 = (Nat.add (Nat.mul x0 y0) x1).
