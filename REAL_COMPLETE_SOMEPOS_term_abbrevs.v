Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term99 (x0 : hreal -> real) (x1 : real -> hreal) := forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (x0 (x1 y0)) = y0.
Definition term65 (x0 : Prop) := False -> x0 -> False.
Definition term181 (x0 : hreal -> real) (x1 : hreal) := fun y0 : real => real_le y0 (x0 x1).
Definition term70 (x0 : Prop) (x1 : Prop) := x0 -> (x0 -> False) -> x1.
Definition term56 (x0 : Prop) (x1 : Prop) := x0 -> (x0 -> True) -> x1.
Definition term86 (x0 : Prop) (x1 : Prop) (x2 : Prop) := ((x1 -> x2) -> x0 -> (x0 -> x1) -> x2) -> (x1 -> x2) -> x0 -> (x0 -> x1) -> x2.
Definition term45 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (y0 -> x1) -> x0 -> (x0 -> y0) -> x1) x2.
Definition term58 (x0 : Prop) := fun y0 : Prop => y0 -> x0 -> y0.
Definition term162 (x0 : hreal) (x1 : hreal -> real) (x2 : hreal) := real_le (x1 x0) (x1 x2).
Definition term33 (x0 : Prop) := imp (~ x0).
Definition term71 (x0 : Prop) (x1 : Prop) := x0 -> (~ x0) -> x1.
Definition term192 (x0 : hreal -> real) := fun y0 : hreal => forall y1 : hreal, (real_le (x0 y0) (x0 y1)) = (hreal_le y0 y1).
Definition term118 (x0 : real -> Prop) (x1 : hreal -> real) := fun y0 : hreal => forall y1 : hreal, (x0 (x1 y1)) -> hreal_le y1 y0.
Definition term117 (x0 : real -> Prop) (x1 : hreal -> real) := fun y0 : hreal => forall y1 : hreal, ((fun y2 : hreal => x0 (x1 y2)) y1) -> hreal_le y1 y0.
Definition term87 (x0 : real -> Prop) (x1 : hreal -> real) := (fun y0 : hreal -> Prop => ((exists y1 : hreal, y0 y1) /\ (exists y1 : hreal, forall y2 : hreal, (y0 y2) -> hreal_le y2 y1)) -> exists y1 : hreal, (forall y2 : hreal, (y0 y2) -> hreal_le y2 y1) /\ (forall y2 : hreal, (forall y3 : hreal, (y0 y3) -> hreal_le y3 y2) -> hreal_le y1 y2)) (fun y0 : hreal => x0 (x1 y0)).
Definition term210 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) (x3 : hreal) := (forall y0 : hreal, (forall y1 : hreal, (x0 (x1 y1)) -> hreal_le y1 y0) -> hreal_le x2 y0) -> hreal_le x2 x3.
Definition term130 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) (x3 : hreal) := (forall y0 : hreal, (x0 (x1 y0)) -> hreal_le y0 x3) -> hreal_le x2 x3.
Definition term129 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) (x3 : hreal) := (forall y0 : hreal, ((fun y1 : hreal => x0 (x1 y1)) y0) -> hreal_le y0 x3) -> hreal_le x2 x3.
Definition term93 (x0 : real -> Prop) (x1 : real) := (x0 x1) /\ (real_le (real_of_num (NUMERAL 0)) x1).
Definition term63 (x0 : Prop) (x1 : Prop) := @eq Prop (x1 -> x0 -> x1).
Definition term23 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 = x0) -> x0 -> y0) x1.
Definition term96 (x0 : real -> hreal) (x1 : hreal -> real) := (forall y0 : hreal, (x0 (x1 y0)) = y0) /\ ((forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (x1 (x0 y0)) = y0) /\ ((forall y0 : hreal, real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (forall y0 : hreal, forall y1 : hreal, (hreal_le y0 y1) = (real_le (x1 y0) (x1 y1))))).
Definition term223 (x0 : real -> hreal) (x1 : hreal -> real) (x2 : hreal) (x3 : real) := (hreal_le x2 (x0 x3)) -> real_le (x1 x2) x3.
Definition term39 := real_of_num (NUMERAL 0).
Definition term132 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) := fun y0 : hreal => (forall y1 : hreal, (x0 (x1 y1)) -> hreal_le y1 y0) -> hreal_le x2 y0.
Definition term131 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) := fun y0 : hreal => (forall y1 : hreal, ((fun y2 : hreal => x0 (x1 y2)) y1) -> hreal_le y1 y0) -> hreal_le x2 y0.
Definition term30 (x0 : Prop) := (False = x0) -> x0 -> False.
Definition term219 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term165 (x0 : hreal -> real) (x1 : hreal) (x2 : real) := imp (real_le (x0 x1) x2).
Definition term152 (x0 : hreal -> real) (x1 : real -> hreal) (x2 : real) := (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (x0 (x1 y0)) = y0) -> (x0 (x1 x2)) = x2.
Definition term80 (x0 : Prop) := False -> (~ False) -> x0.
Definition term91 (x0 : real -> Prop) := exists y0 : real, forall y1 : real, (x0 y1) -> real_le y1 y0.
Definition term14 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> forall y0 : real, forall y1 : real, (exists y2 : real, (real_le y0 y2) /\ (real_le y2 y1)) -> real_le y0 y1.
Definition term9 (x0 : real) (x1 : real) := exists y0 : real, (real_le x0 y0) /\ (real_le y0 x1).
Definition term150 (x0 : hreal -> real) (x1 : real -> hreal) (x2 : real) := (real_le (real_of_num (NUMERAL 0)) x2) -> (x0 (x1 x2)) = x2.
Definition term10 (x0 : real) (x1 : real) := fun y0 : real => (real_le x0 y0) /\ (real_le y0 x1).
Definition term233 := fun y0 : real -> hreal => exists y1 : hreal -> real, (forall y2 : hreal, (y0 (y1 y2)) = y2) /\ ((forall y2 : real, (real_le (real_of_num (NUMERAL 0)) y2) -> (y1 (y0 y2)) = y2) /\ ((forall y2 : hreal, real_le (real_of_num (NUMERAL 0)) (y1 y2)) /\ (forall y2 : hreal, forall y3 : hreal, (hreal_le y2 y3) = (real_le (y1 y2) (y1 y3))))).
Definition term229 (x0 : real -> Prop) := fun y0 : real => (forall y1 : real, (x0 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x0 y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term111 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) (x3 : hreal) := ((fun y0 : hreal => x0 (x1 y0)) x2) -> hreal_le x2 x3.
Definition term95 (x0 : real -> hreal) := exists y0 : hreal -> real, (forall y1 : hreal, (x0 (y0 y1)) = y1) /\ ((forall y1 : real, (real_le (real_of_num (NUMERAL 0)) y1) -> (y0 (x0 y1)) = y1) /\ ((forall y1 : hreal, real_le (real_of_num (NUMERAL 0)) (y0 y1)) /\ (forall y1 : hreal, forall y2 : hreal, (hreal_le y1 y2) = (real_le (y0 y1) (y0 y2))))).
Definition term101 (x0 : hreal -> real) := forall y0 : hreal, real_le (real_of_num (NUMERAL 0)) (x0 y0).
Definition term196 (x0 : real -> hreal) (x1 : real) (x2 : hreal) := hreal_le (x0 x1) x2.
Definition term43 (x0 : real) := real_le x0 (real_of_num (NUMERAL 0)).
Definition term69 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term109 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) := imp ((fun y0 : hreal => x0 (x1 y0)) x2).
Definition term31 (x0 : Prop) := imp (True = x0).
Definition term79 (x0 : Prop) := (fun y0 : Prop => y0 -> (~ y0) -> x0) False.
Definition term222 (x0 : hreal) (x1 : hreal -> real) (x2 : real -> hreal) (x3 : real) := imp (real_le (x1 x0) (x1 (x2 x3))).
Definition term161 (x0 : hreal) (x1 : hreal -> real) (x2 : hreal) := (fun y0 : hreal => (hreal_le x0 y0) = (real_le (x1 x0) (x1 y0))) x2.
Definition term218 := forall y0 : hreal, True.
Definition term108 (x0 : real -> Prop) (x1 : hreal -> real) := and (exists y0 : hreal, x0 (x1 y0)).
Definition term141 (x0 : real -> Prop) (x1 : hreal -> real) := ((exists y0 : hreal, x0 (x1 y0)) /\ (exists y0 : hreal, forall y1 : hreal, (x0 (x1 y1)) -> hreal_le y1 y0)) -> exists y0 : hreal, (forall y1 : hreal, (x0 (x1 y1)) -> hreal_le y1 y0) /\ (forall y1 : hreal, (forall y2 : hreal, (x0 (x1 y2)) -> hreal_le y2 y1) -> hreal_le y0 y1).
Definition term89 (x0 : real -> Prop) (x1 : hreal -> real) := ((exists y0 : hreal, (fun y1 : hreal => x0 (x1 y1)) y0) /\ (exists y0 : hreal, forall y1 : hreal, ((fun y2 : hreal => x0 (x1 y2)) y1) -> hreal_le y1 y0)) -> exists y0 : hreal, (forall y1 : hreal, ((fun y2 : hreal => x0 (x1 y2)) y1) -> hreal_le y1 y0) /\ (forall y1 : hreal, (forall y2 : hreal, ((fun y3 : hreal => x0 (x1 y3)) y2) -> hreal_le y2 y1) -> hreal_le y0 y1).
Definition term38 := (fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) (real_of_num (NUMERAL 0)).
Definition term40 := forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) \/ (real_le y0 (real_of_num (NUMERAL 0))).
Definition term83 (x0 : Prop) := (~ False) -> x0.
Definition term13 := forall y0 : real, forall y1 : real, (exists y2 : real, (real_le y0 y2) /\ (real_le y2 y1)) -> real_le y0 y1.
Definition term2 (x0 : real) := forall y0 : real, forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1.
Definition term0 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2.
Definition term106 (x0 : real -> Prop) (x1 : hreal -> real) := exists y0 : hreal, x0 (x1 y0).
Definition term163 (x0 : hreal) (x1 : real -> hreal) (x2 : real) := hreal_le x0 (x1 x2).
Definition term189 (x0 : hreal -> real) (x1 : hreal) := fun y0 : hreal => (real_le (x0 x1) (x0 y0)) = (hreal_le x1 y0).
Definition term178 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) (x3 : real -> hreal) (x4 : real) := (x0 (x1 x2)) -> hreal_le x2 (x3 x4).
Definition term225 (x0 : real -> hreal) (x1 : hreal -> real) (x2 : hreal) (x3 : real) := ((real_le (x1 x2) (x1 (x0 x3))) = (real_le (x1 x2) x3)) -> (real_le (x1 x2) (x1 (x0 x3))) -> real_le (x1 x2) x3.
Definition term179 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : real -> hreal) (x3 : real) := forall y0 : hreal, (x0 (x1 y0)) -> hreal_le y0 (x2 x3).
Definition term177 (x0 : real) := fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 x0).
Definition term6 (x0 : real) (x1 : real) (x2 : real) := ((real_le x1 x0) /\ (real_le x0 x2)) -> real_le x1 x2.
Definition term52 (x0 : Prop) (x1 : Prop) := (False -> x1) -> x0 -> (x0 -> False) -> x1.
Definition term47 (x0 : Prop) (x1 : Prop) := (True -> x1) -> x0 -> (x0 -> True) -> x1.
Definition term72 (x0 : Prop) (x1 : Prop) := True -> x0 -> (~ x0) -> x1.
Definition term151 (x0 : hreal -> real) (x1 : real -> hreal) (x2 : real) := x0 (x1 x2).
Definition term49 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x1 -> x2) -> x0 -> (x0 -> x1) -> x2.
Definition term180 (x0 : hreal -> real) (x1 : real -> Prop) := ((exists y0 : hreal, (forall y1 : hreal, (x1 (x0 y1)) -> hreal_le y1 y0) /\ (forall y1 : hreal, (forall y2 : hreal, (x1 (x0 y2)) -> hreal_le y2 y1) -> hreal_le y0 y1)) -> exists y0 : real, (forall y1 : real, (x1 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x1 y2) -> real_le y2 y1) -> real_le y0 y1)) -> ((exists y0 : hreal, x1 (x0 y0)) /\ (exists y0 : hreal, forall y1 : hreal, (x1 (x0 y1)) -> hreal_le y1 y0)) -> (((exists y0 : hreal, x1 (x0 y0)) /\ (exists y0 : hreal, forall y1 : hreal, (x1 (x0 y1)) -> hreal_le y1 y0)) -> exists y0 : hreal, (forall y1 : hreal, (x1 (x0 y1)) -> hreal_le y1 y0) /\ (forall y1 : hreal, (forall y2 : hreal, (x1 (x0 y2)) -> hreal_le y2 y1) -> hreal_le y0 y1)) -> exists y0 : real, (forall y1 : real, (x1 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x1 y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term27 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 -> x1.
Definition term171 (x0 : real) := and (real_le (real_of_num (NUMERAL 0)) x0).
Definition term138 (x0 : real -> Prop) (x1 : hreal -> real) := fun y0 : hreal => (forall y1 : hreal, (x0 (x1 y1)) -> hreal_le y1 y0) /\ (forall y1 : hreal, (forall y2 : hreal, (x0 (x1 y2)) -> hreal_le y2 y1) -> hreal_le y0 y1).
Definition term137 (x0 : real -> Prop) (x1 : hreal -> real) := fun y0 : hreal => (forall y1 : hreal, ((fun y2 : hreal => x0 (x1 y2)) y1) -> hreal_le y1 y0) /\ (forall y1 : hreal, (forall y2 : hreal, ((fun y3 : hreal => x0 (x1 y3)) y2) -> hreal_le y2 y1) -> hreal_le y0 y1).
Definition term103 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) := x0 (x1 x2).
Definition term112 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) (x3 : hreal) := (x0 (x1 x2)) -> hreal_le x2 x3.
Definition term235 (x0 : real -> Prop) := fun y0 : real => (x0 y0) /\ (real_le (real_of_num (NUMERAL 0)) y0).
Definition term19 (x0 : Prop) (x1 : Prop) := ((x0 = x1) -> x0 -> x1) -> (x0 = x1) -> x0 -> x1.
Definition term209 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) (x3 : hreal) := (fun y0 : hreal => (forall y1 : hreal, (x0 (x1 y1)) -> hreal_le y1 y0) -> hreal_le x2 y0) x3.
Definition term51 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 -> x1) -> x0 -> (x0 -> y0) -> x1) False.
Definition term73 (x0 : Prop) := fun y0 : Prop => y0 -> (~ y0) -> x0.
Definition term170 (x0 : real) := (exists y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 x0)) -> real_le (real_of_num (NUMERAL 0)) x0.
Definition term182 (x0 : hreal -> real) (x1 : hreal) (x2 : real) := (fun y0 : real => real_le y0 (x0 x1)) x2.
Definition term66 (x0 : Prop) := imp (False -> x0).
Definition term90 (x0 : real -> Prop) := (exists y0 : real, (x0 y0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (exists y0 : real, forall y1 : real, (x0 y1) -> real_le y1 y0).
Definition term8 (x0 : real) (x1 : real) := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> real_le x0 x1.
Definition term12 (x0 : real) := forall y0 : real, (exists y1 : real, (real_le x0 y1) /\ (real_le y1 y0)) -> real_le x0 y0.
Definition term75 (x0 : Prop) := (fun y0 : Prop => y0 -> (~ y0) -> x0) True.
Definition term201 (x0 : hreal -> real) (x1 : hreal) := (fun y0 : hreal => real_le (real_of_num (NUMERAL 0)) (x0 y0)) x1.
Definition term227 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) := forall y0 : real, (forall y1 : real, (x0 y1) -> real_le y1 y0) -> real_le (x1 x2) y0.
Definition term97 (x0 : real -> hreal) (x1 : hreal -> real) := (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (x1 (x0 y0)) = y0) /\ ((forall y0 : hreal, real_le (real_of_num (NUMERAL 0)) (x1 y0)) /\ (forall y0 : hreal, forall y1 : hreal, (hreal_le y0 y1) = (real_le (x1 y0) (x1 y1)))).
Definition term11 (x0 : real) (x1 : real) := (exists y0 : real, (real_le x0 y0) /\ (real_le y0 x1)) -> real_le x0 x1.
Definition term134 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) := forall y0 : hreal, (forall y1 : hreal, (x0 (x1 y1)) -> hreal_le y1 y0) -> hreal_le x2 y0.
Definition term133 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) := forall y0 : hreal, (forall y1 : hreal, ((fun y2 : hreal => x0 (x1 y2)) y1) -> hreal_le y1 y0) -> hreal_le x2 y0.
Definition term213 (x0 : real -> Prop) (x1 : hreal) (x2 : hreal -> real) (x3 : real -> hreal) (x4 : real) := (x0 (x2 x1)) -> real_le (x2 x1) (x2 (x3 x4)).
Definition term193 (x0 : hreal -> real) := forall y0 : hreal, forall y1 : hreal, (real_le (x0 y0) (x0 y1)) = (hreal_le y0 y1).
Definition term100 (x0 : hreal -> real) := forall y0 : hreal, forall y1 : hreal, (hreal_le y0 y1) = (real_le (x0 y0) (x0 y1)).
Definition term200 (x0 : real) (x1 : hreal -> real) (x2 : hreal) := (exists y0 : real, (real_le x0 y0) /\ (real_le y0 (x1 x2))) -> real_le x0 (x1 x2).
Definition term147 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : real -> hreal) (x3 : real) := ((x0 (x1 (x2 x3))) = (x0 x3)) -> (x0 x3) -> x0 (x1 (x2 x3)).
Definition term164 (x0 : hreal) (x1 : hreal -> real) (x2 : real -> hreal) (x3 : real) := real_le (x1 x0) (x1 (x2 x3)).
Definition term50 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop ((x1 -> x2) -> x0 -> (x0 -> x1) -> x2).
Definition term236 (x0 : real -> Prop) := ((exists y0 : real, (x0 y0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (exists y0 : real, forall y1 : real, (x0 y1) -> real_le y1 y0)) -> exists y0 : real, (forall y1 : real, (x0 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x0 y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term228 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) := (forall y0 : real, (x0 y0) -> real_le y0 (x1 x2)) /\ (forall y0 : real, (forall y1 : real, (x0 y1) -> real_le y1 y0) -> real_le (x1 x2) y0).
Definition term128 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) := imp (forall y0 : hreal, (x0 (x1 y0)) -> hreal_le y0 x2).
Definition term127 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) := imp (forall y0 : hreal, ((fun y1 : hreal => x0 (x1 y1)) y0) -> hreal_le y0 x2).
Definition term116 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) := forall y0 : hreal, (x0 (x1 y0)) -> hreal_le y0 x2.
Definition term124 (x0 : real -> Prop) (x1 : hreal -> real) := imp ((exists y0 : hreal, x0 (x1 y0)) /\ (exists y0 : hreal, forall y1 : hreal, (x0 (x1 y1)) -> hreal_le y1 y0)).
Definition term123 (x0 : real -> Prop) (x1 : hreal -> real) := imp ((exists y0 : hreal, (fun y1 : hreal => x0 (x1 y1)) y0) /\ (exists y0 : hreal, forall y1 : hreal, ((fun y2 : hreal => x0 (x1 y2)) y1) -> hreal_le y1 y0)).
Definition term176 (x0 : real) := exists y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 x0).
Definition term17 (x0 : Prop) (x1 : Prop) := (x0 = x1) -> x0 -> x1.
Definition term55 (x0 : Prop) (x1 : Prop) := (x0 -> True) -> x1.
Definition term98 (x0 : hreal -> real) := (forall y0 : hreal, real_le (real_of_num (NUMERAL 0)) (x0 y0)) /\ (forall y0 : hreal, forall y1 : hreal, (hreal_le y0 y1) = (real_le (x0 y0) (x0 y1))).
Definition term166 (x0 : hreal -> real) (x1 : hreal) (x2 : real -> hreal) (x3 : real) := (real_le (x0 x1) x3) -> hreal_le x1 (x2 x3).
Definition term115 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) := forall y0 : hreal, ((fun y1 : hreal => x0 (x1 y1)) y0) -> hreal_le y0 x2.
Definition term25 (x0 : Prop) := (True = x0) -> x0 -> True.
Definition term158 (x0 : hreal -> real) (x1 : hreal) (x2 : real) := real_le (x0 x1) x2.
Definition term234 (x0 : real -> Prop) := fun y0 : real => forall y1 : real, (x0 y1) -> real_le y1 y0.
Definition term231 (x0 : hreal -> real) (x1 : real -> Prop) := ((exists y0 : hreal, x1 (x0 y0)) /\ (exists y0 : hreal, forall y1 : hreal, (x1 (x0 y1)) -> hreal_le y1 y0)) -> (((exists y0 : hreal, x1 (x0 y0)) /\ (exists y0 : hreal, forall y1 : hreal, (x1 (x0 y1)) -> hreal_le y1 y0)) -> exists y0 : hreal, (forall y1 : hreal, (x1 (x0 y1)) -> hreal_le y1 y0) /\ (forall y1 : hreal, (forall y2 : hreal, (x1 (x0 y2)) -> hreal_le y2 y1) -> hreal_le y0 y1)) -> exists y0 : real, (forall y1 : real, (x1 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x1 y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term185 (x0 : hreal -> real) (x1 : hreal) (x2 : real) := @eq Prop ((fun y0 : real => real_le y0 (x0 x1)) x2).
Definition term15 (x0 : real) := (fun y0 : real => forall y1 : real, (exists y2 : real, (real_le y0 y2) /\ (real_le y2 y1)) -> real_le y0 y1) x0.
Definition term174 (x0 : real -> Prop) (x1 : real) (x2 : real) := (forall y0 : real, (x0 y0) -> real_le y0 x2) -> real_le x1 x2.
Definition term226 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) (x3 : real) := (forall y0 : real, (x0 y0) -> real_le y0 x3) -> real_le (x1 x2) x3.
Definition term184 (x0 : real -> hreal) (x1 : real) (x2 : hreal -> real) (x3 : hreal) := real_le (x2 (x0 x1)) (x2 x3).
Definition term205 (x0 : real) (x1 : hreal -> real) (x2 : hreal) := exists y0 : real, (real_le x0 y0) /\ (real_le y0 (x1 x2)).
Definition term230 (x0 : hreal -> real) (x1 : real -> Prop) := (exists y0 : hreal, (forall y1 : hreal, (x1 (x0 y1)) -> hreal_le y1 y0) /\ (forall y1 : hreal, (forall y2 : hreal, (x1 (x0 y2)) -> hreal_le y2 y1) -> hreal_le y0 y1)) -> exists y0 : real, (forall y1 : real, (x1 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x1 y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term140 (x0 : real -> Prop) (x1 : hreal -> real) := exists y0 : hreal, (forall y1 : hreal, (x0 (x1 y1)) -> hreal_le y1 y0) /\ (forall y1 : hreal, (forall y2 : hreal, (x0 (x1 y2)) -> hreal_le y2 y1) -> hreal_le y0 y1).
Definition term139 (x0 : real -> Prop) (x1 : hreal -> real) := exists y0 : hreal, (forall y1 : hreal, ((fun y2 : hreal => x0 (x1 y2)) y1) -> hreal_le y1 y0) /\ (forall y1 : hreal, (forall y2 : hreal, ((fun y3 : hreal => x0 (x1 y3)) y2) -> hreal_le y2 y1) -> hreal_le y0 y1).
Definition term207 (x0 : real -> Prop) (x1 : real) (x2 : hreal -> real) (x3 : hreal) := (x0 x1) -> real_le x1 (x2 x3).
Definition term78 (x0 : Prop) (x1 : Prop) := @eq Prop (x0 -> (~ x0) -> x1).
Definition term59 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => y0 -> x0 -> y0) x1.
Definition term77 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => y0 -> (~ y0) -> x0) x1).
Definition term62 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => y0 -> x0 -> y0) x1).
Definition term26 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => (y0 = x0) -> x0 -> y0) x1).
Definition term204 (x0 : real) (x1 : hreal -> real) (x2 : hreal) := (real_le x0 (real_of_num (NUMERAL 0))) /\ (real_le (real_of_num (NUMERAL 0)) (x1 x2)).
Definition term144 (x0 : real -> Prop) := exists y0 : real, (forall y1 : real, (x0 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x0 y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term37 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term232 (x0 : real -> hreal) := fun y0 : hreal -> real => (forall y1 : hreal, (x0 (y0 y1)) = y1) /\ ((forall y1 : real, (real_le (real_of_num (NUMERAL 0)) y1) -> (y0 (x0 y1)) = y1) /\ ((forall y1 : hreal, real_le (real_of_num (NUMERAL 0)) (y0 y1)) /\ (forall y1 : hreal, forall y2 : hreal, (hreal_le y1 y2) = (real_le (y0 y1) (y0 y2))))).
Definition term215 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : real -> hreal) (x3 : real) := fun y0 : hreal => (x0 (x1 y0)) -> real_le (x1 y0) (x1 (x2 x3)).
Definition term175 (x0 : real -> Prop) (x1 : real) := (forall y0 : real, (x0 y0) -> real_le y0 x1) -> forall y0 : real, (x0 y0) -> real_le y0 x1.
Definition term153 (x0 : hreal -> real) (x1 : real -> hreal) := (forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (x0 (x1 y0)) = y0) -> forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) -> (x0 (x1 y0)) = y0.
Definition term216 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : real -> hreal) (x3 : real) := forall y0 : hreal, (x0 (x1 y0)) -> real_le (x1 y0) (x1 (x2 x3)).
Definition term195 (x0 : hreal -> real) (x1 : hreal) (x2 : hreal) := (fun y0 : hreal => (real_le (x0 x1) (x0 y0)) = (hreal_le x1 y0)) x2.
Definition term220 (x0 : Prop) := forall y0 : hreal, x0.
Definition term92 (x0 : real -> Prop) := exists y0 : real, (x0 y0) /\ (real_le (real_of_num (NUMERAL 0)) y0).
Definition term191 (x0 : hreal -> real) := fun y0 : hreal => forall y1 : hreal, (hreal_le y0 y1) = (real_le (x0 y0) (x0 y1)).
Definition term155 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (x0 y0) -> real_le y0 x1) x2.
Definition term28 (x0 : Prop) (x1 : Prop) := @eq Prop ((x1 = x0) -> x0 -> x1).
Definition term34 (x0 : Prop) := (~ x0) -> ~ x0.
Definition term186 (x0 : real) (x1 : hreal -> real) (x2 : hreal) := real_le x0 (x1 x2).
Definition term212 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) (x3 : real -> hreal) (x4 : real) := (forall y0 : hreal, (x0 (x1 y0)) -> hreal_le y0 (x3 x4)) -> hreal_le x2 (x3 x4).
Definition term21 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term122 (x0 : real -> Prop) (x1 : hreal -> real) := (exists y0 : hreal, x0 (x1 y0)) /\ (exists y0 : hreal, forall y1 : hreal, (x0 (x1 y1)) -> hreal_le y1 y0).
Definition term53 (x0 : Prop) := imp (True -> x0).
Definition term3 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1) x1.
Definition term54 (x0 : Prop) := imp (x0 -> True).
Definition term190 (x0 : hreal -> real) (x1 : hreal) := forall y0 : hreal, (real_le (x0 x1) (x0 y0)) = (hreal_le x1 y0).
Definition term29 (x0 : Prop) := (fun y0 : Prop => (y0 = x0) -> x0 -> y0) False.
Definition term136 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) := (forall y0 : hreal, (x0 (x1 y0)) -> hreal_le y0 x2) /\ (forall y0 : hreal, (forall y1 : hreal, (x0 (x1 y1)) -> hreal_le y1 y0) -> hreal_le x2 y0).
Definition term135 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) := (forall y0 : hreal, ((fun y1 : hreal => x0 (x1 y1)) y0) -> hreal_le y0 x2) /\ (forall y0 : hreal, (forall y1 : hreal, ((fun y2 : hreal => x0 (x1 y2)) y1) -> hreal_le y1 y0) -> hreal_le x2 y0).
Definition term32 (x0 : Prop) := imp (False = x0).
Definition term60 (x0 : Prop) := (fun y0 : Prop => y0 -> x0 -> y0) True.
Definition term146 (x0 : hreal -> real) (x1 : real -> Prop) := (((exists y0 : hreal, x1 (x0 y0)) /\ (exists y0 : hreal, forall y1 : hreal, (x1 (x0 y1)) -> hreal_le y1 y0)) -> exists y0 : hreal, (forall y1 : hreal, (x1 (x0 y1)) -> hreal_le y1 y0) /\ (forall y1 : hreal, (forall y2 : hreal, (x1 (x0 y2)) -> hreal_le y2 y1) -> hreal_le y0 y1)) -> exists y0 : real, (forall y1 : real, (x1 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x1 y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term145 (x0 : hreal -> real) (x1 : real -> Prop) := (((exists y0 : hreal, (fun y1 : hreal => x1 (x0 y1)) y0) /\ (exists y0 : hreal, forall y1 : hreal, ((fun y2 : hreal => x1 (x0 y2)) y1) -> hreal_le y1 y0)) -> exists y0 : hreal, (forall y1 : hreal, ((fun y2 : hreal => x1 (x0 y2)) y1) -> hreal_le y1 y0) /\ (forall y1 : hreal, (forall y2 : hreal, ((fun y3 : hreal => x1 (x0 y3)) y2) -> hreal_le y2 y1) -> hreal_le y0 y1)) -> exists y0 : real, (forall y1 : real, (x1 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x1 y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term85 (x0 : Prop) (x1 : Prop) (x2 : Prop) := ((x1 -> x2) -> x0 -> (x0 -> x1) -> x2) -> x0 -> (x0 -> x1) -> x2.
Definition term113 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) := fun y0 : hreal => ((fun y1 : hreal => x0 (x1 y1)) y0) -> hreal_le y0 x2.
Definition term202 (x0 : hreal -> real) (x1 : hreal) := real_le (real_of_num (NUMERAL 0)) (x0 x1).
Definition term237 := forall y0 : real -> Prop, ((exists y1 : real, (y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y1)) /\ (exists y1 : real, forall y2 : real, (y0 y2) -> real_le y2 y1)) -> exists y1 : real, (forall y2 : real, (y0 y2) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (y0 y3) -> real_le y3 y2) -> real_le y1 y2).
Definition term5 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0) x2.
Definition term36 (x0 : Prop) (x1 : Prop) := ((x1 = x0) -> x0 -> x1) -> (x1 = x0) -> x0 -> x1.
Definition term24 (x0 : Prop) := (fun y0 : Prop => (y0 = x0) -> x0 -> y0) True.
Definition term105 (x0 : real -> Prop) (x1 : hreal -> real) := exists y0 : hreal, (fun y1 : hreal => x0 (x1 y1)) y0.
Definition term206 (x0 : real) (x1 : hreal -> real) (x2 : hreal) := fun y0 : real => (real_le x0 y0) /\ (real_le y0 (x1 x2)).
Definition term194 (x0 : hreal -> real) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, (real_le (x0 y0) (x0 y1)) = (hreal_le y0 y1)) x1.
Definition term159 (x0 : hreal -> real) (x1 : hreal) := (fun y0 : hreal => forall y1 : hreal, (hreal_le y0 y1) = (real_le (x0 y0) (x0 y1))) x1.
Definition term42 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) \/ (real_le x0 (real_of_num (NUMERAL 0))).
Definition term169 (x0 : hreal -> real) (x1 : hreal) := real_le (x0 x1).
Definition term143 (x0 : real -> Prop) (x1 : hreal -> real) := imp (((exists y0 : hreal, x0 (x1 y0)) /\ (exists y0 : hreal, forall y1 : hreal, (x0 (x1 y1)) -> hreal_le y1 y0)) -> exists y0 : hreal, (forall y1 : hreal, (x0 (x1 y1)) -> hreal_le y1 y0) /\ (forall y1 : hreal, (forall y2 : hreal, (x0 (x1 y2)) -> hreal_le y2 y1) -> hreal_le y0 y1)).
Definition term142 (x0 : real -> Prop) (x1 : hreal -> real) := imp (((exists y0 : hreal, (fun y1 : hreal => x0 (x1 y1)) y0) /\ (exists y0 : hreal, forall y1 : hreal, ((fun y2 : hreal => x0 (x1 y2)) y1) -> hreal_le y1 y0)) -> exists y0 : hreal, (forall y1 : hreal, ((fun y2 : hreal => x0 (x1 y2)) y1) -> hreal_le y1 y0) /\ (forall y1 : hreal, (forall y2 : hreal, ((fun y3 : hreal => x0 (x1 y3)) y2) -> hreal_le y2 y1) -> hreal_le y0 y1)).
Definition term16 (x0 : real) (x1 : real) := (fun y0 : real => (exists y1 : real, (real_le x0 y1) /\ (real_le y1 y0)) -> real_le x0 y0) x1.
Definition term183 (x0 : hreal) (x1 : hreal -> real) (x2 : real -> hreal) (x3 : real) := (fun y0 : real => real_le y0 (x1 x0)) (x1 (x2 x3)).
Definition term22 (x0 : Prop) := fun y0 : Prop => (y0 = x0) -> x0 -> y0.
Definition term74 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => y0 -> (~ y0) -> x0) x1.
Definition term208 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) := forall y0 : real, (x0 y0) -> real_le y0 (x1 x2).
Definition term84 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> (x0 -> x1) -> x2.
Definition term149 (x0 : hreal -> real) (x1 : real -> hreal) (x2 : real) := (fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) -> (x0 (x1 y0)) = y0) x2.
Definition term57 (x0 : Prop) (x1 : Prop) := x1 -> x0 -> x1.
Definition term199 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : real -> hreal) (x3 : real) (x4 : hreal) := (x0 (x1 (x2 x3))) -> hreal_le (x2 x3) x4.
Definition term120 (x0 : real -> Prop) (x1 : hreal -> real) := exists y0 : hreal, forall y1 : hreal, (x0 (x1 y1)) -> hreal_le y1 y0.
Definition term119 (x0 : real -> Prop) (x1 : hreal -> real) := exists y0 : hreal, forall y1 : hreal, ((fun y2 : hreal => x0 (x1 y2)) y1) -> hreal_le y1 y0.
Definition term67 (x0 : Prop) := imp (x0 -> False).
Definition term4 (x0 : real) (x1 : real) := forall y0 : real, ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0.
Definition term114 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) := fun y0 : hreal => (x0 (x1 y0)) -> hreal_le y0 x2.
Definition term68 (x0 : Prop) (x1 : Prop) := (x0 -> False) -> x1.
Definition term154 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : real -> hreal) (x3 : real) := (x0 x3) -> x0 (x1 (x2 x3)).
Definition term104 (x0 : real -> Prop) (x1 : hreal -> real) := fun y0 : hreal => (fun y1 : hreal => x0 (x1 y1)) y0.
Definition term173 (x0 : real) (x1 : real) := True /\ (real_le x0 x1).
Definition term187 (x0 : real) (x1 : hreal -> real) (x2 : hreal) := @eq Prop (real_le x0 (x1 x2)).
Definition term7 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x1) /\ (real_le x1 x2).
Definition term76 (x0 : Prop) := True -> (~ True) -> x0.
Definition term148 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : real -> hreal) (x3 : real) := x0 (x1 (x2 x3)).
Definition term217 := fun y0 : hreal => True.
Definition term203 (x0 : real) := and (real_le x0 (real_of_num (NUMERAL 0))).
Definition term88 (x0 : real -> Prop) (x1 : hreal -> real) := fun y0 : hreal => x0 (x1 y0).
Definition term224 (x0 : real -> hreal) (x1 : hreal -> real) (x2 : hreal) (x3 : real) := (real_le (x1 x2) (x1 (x0 x3))) -> real_le (x1 x2) x3.
Definition term94 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (x0 y0) -> real_le y0 x1.
Definition term102 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) := (fun y0 : hreal => x0 (x1 y0)) x2.
Definition term81 (x0 : Prop) := (~ True) -> x0.
Definition term35 (x0 : Prop) (x1 : Prop) := ((x1 = x0) -> x0 -> x1) -> x0 -> x1.
Definition term18 (x0 : Prop) (x1 : Prop) := ((x0 = x1) -> x0 -> x1) -> x0 -> x1.
Definition term82 := imp (~ True).
Definition term167 (x0 : hreal) (x1 : hreal -> real) (x2 : real -> hreal) (x3 : real) := (real_le (x1 x0) x3) -> real_le (x1 x0) (x1 (x2 x3)).
Definition term221 (x0 : hreal) (x1 : real -> hreal) (x2 : real) := imp (hreal_le x0 (x1 x2)).
Definition term197 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) (x3 : hreal) := (fun y0 : hreal => (x0 (x1 y0)) -> hreal_le y0 x2) x3.
Definition term20 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term168 (x0 : hreal) (x1 : hreal -> real) (x2 : real -> hreal) (x3 : real) := ((real_le (x1 x0) (x1 (x2 x3))) = (real_le (x1 x0) x3)) -> (real_le (x1 x0) x3) -> real_le (x1 x0) (x1 (x2 x3)).
Definition term44 (x0 : Prop) (x1 : Prop) := fun y0 : Prop => (y0 -> x1) -> x0 -> (x0 -> y0) -> x1.
Definition term211 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) := (forall y0 : hreal, (forall y1 : hreal, (x0 (x1 y1)) -> hreal_le y1 y0) -> hreal_le x2 y0) -> forall y0 : hreal, (forall y1 : hreal, (x0 (x1 y1)) -> hreal_le y1 y0) -> hreal_le x2 y0.
Definition term198 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) := (forall y0 : hreal, (x0 (x1 y0)) -> hreal_le y0 x2) -> forall y0 : hreal, (x0 (x1 y0)) -> hreal_le y0 x2.
Definition term1 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) x0.
Definition term160 (x0 : hreal) (x1 : hreal -> real) := forall y0 : hreal, (hreal_le x0 y0) = (real_le (x1 x0) (x1 y0)).
Definition term110 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) := imp (x0 (x1 x2)).
Definition term188 (x0 : hreal) (x1 : hreal -> real) := fun y0 : hreal => (hreal_le x0 y0) = (real_le (x1 x0) (x1 y0)).
Definition term107 (x0 : real -> Prop) (x1 : hreal -> real) := and (exists y0 : hreal, (fun y1 : hreal => x0 (x1 y1)) y0).
Definition term214 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : real -> hreal) (x3 : real) := fun y0 : hreal => (x0 (x1 y0)) -> hreal_le y0 (x2 x3).
Definition term172 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 x1).
Definition term41 (x0 : real) := (fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) \/ (real_le y0 (real_of_num (NUMERAL 0)))) x0.
Definition term46 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 -> x1) -> x0 -> (x0 -> y0) -> x1) True.
Definition term126 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) := and (forall y0 : hreal, (x0 (x1 y0)) -> hreal_le y0 x2).
Definition term125 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) := and (forall y0 : hreal, ((fun y1 : hreal => x0 (x1 y1)) y0) -> hreal_le y0 x2).
Definition term61 (x0 : Prop) := True -> x0 -> True.
Definition term157 (x0 : real -> Prop) (x1 : hreal -> real) (x2 : hreal) (x3 : real) := (x0 (x1 x2)) -> real_le (x1 x2) x3.
Definition term121 (x0 : real -> Prop) (x1 : hreal -> real) := (exists y0 : hreal, (fun y1 : hreal => x0 (x1 y1)) y0) /\ (exists y0 : hreal, forall y1 : hreal, ((fun y2 : hreal => x0 (x1 y2)) y1) -> hreal_le y1 y0).
Definition term48 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop ((fun y0 : Prop => (y0 -> x1) -> x0 -> (x0 -> y0) -> x1) x2).
Definition term64 (x0 : Prop) := (fun y0 : Prop => y0 -> x0 -> y0) False.
Definition term156 (x0 : real -> Prop) (x1 : real) (x2 : real) := (x0 x1) -> real_le x1 x2.
