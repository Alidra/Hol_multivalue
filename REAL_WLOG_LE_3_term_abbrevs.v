Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term209 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (real_le x2 x3) /\ (~ (x0 x1 x2 x3)).
Definition term31 (x0 : type1624) (x1 : real) (x2 : real) := fun y0 : real => ((real_le x1 x2) /\ (real_le x2 y0)) -> x0 x1 x2 y0.
Definition term138 (x0 : type1624) (x1 : real) (x2 : real) := exists y0 : real, ((forall y1 : real, forall y2 : real, forall y3 : real, (~ (x0 y1 y2 y3)) \/ ((x0 y2 y1 y3) /\ (x0 y1 y3 y2))) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y3))) \/ (x0 y1 y2 y3))) /\ ((fun y1 : real => ~ (x0 x1 x2 y1)) y0).
Definition term126 (x0 : type1624) (x1 : real) := exists y0 : real, ((forall y1 : real, forall y2 : real, forall y3 : real, (~ (x0 y1 y2 y3)) \/ ((x0 y2 y1 y3) /\ (x0 y1 y3 y2))) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y3))) \/ (x0 y1 y2 y3))) /\ ((fun y1 : real => exists y2 : real, ~ (x0 x1 y1 y2)) y0).
Definition term114 (x0 : type1624) := exists y0 : real, ((forall y1 : real, forall y2 : real, forall y3 : real, (~ (x0 y1 y2 y3)) \/ ((x0 y2 y1 y3) /\ (x0 y1 y3 y2))) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y3))) \/ (x0 y1 y2 y3))) /\ ((fun y1 : real => exists y2 : real, exists y3 : real, ~ (x0 y1 y2 y3)) y0).
Definition term179 (x0 : real) (x1 : real) := (~ (real_le x0 x1)) -> real_le x0 x1.
Definition term101 (x0 : type1013) := ~ (all x0).
Definition term72 (x0 : real -> Prop) := ~ (all x0).
Definition term233 := (~ False) -> False.
Definition term11 := (~ (forall y0 : type1624, ((forall y1 : real, forall y2 : real, forall y3 : real, (y0 y1 y2 y3) -> (y0 y2 y1 y3) /\ (y0 y1 y3 y2)) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> y0 y1 y2 y3)) -> forall y1 : real, forall y2 : real, forall y3 : real, y0 y1 y2 y3)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term145 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := ((forall y0 : real, forall y1 : real, forall y2 : real, (~ (x0 y0 y1 y2)) \/ ((x0 y1 y0 y2) /\ (x0 y0 y2 y1))) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (x0 y0 y1 y2))) /\ (~ (x0 x1 x2 x3)).
Definition term77 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := ~ ((fun y0 : real => x0 x1 x2 y0) x3).
Definition term115 (x0 : type1624) (x1 : real) := (fun y0 : real => exists y1 : real, exists y2 : real, ~ (x0 y0 y1 y2)) x1.
Definition term59 (x0 : real) (x1 : real) (x2 : real) := or (~ ((real_le x0 x1) /\ (real_le x1 x2))).
Definition term30 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := ((real_le x1 x2) /\ (real_le x2 x3)) -> x0 x1 x2 x3.
Definition term198 (x0 : Prop) := ~ (~ x0).
Definition term146 (x0 : type1624) (x1 : real) (x2 : real) := fun y0 : real => ((forall y1 : real, forall y2 : real, forall y3 : real, (~ (x0 y1 y2 y3)) \/ ((x0 y2 y1 y3) /\ (x0 y1 y3 y2))) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y3))) \/ (x0 y1 y2 y3))) /\ ((fun y1 : real => ~ (x0 x1 x2 y1)) y0).
Definition term70 (x0 : type1624) := and (forall y0 : real, forall y1 : real, forall y2 : real, (~ (x0 y0 y1 y2)) \/ ((x0 y1 y0 y2) /\ (x0 y0 y2 y1))).
Definition term44 (x0 : type1624) := and (forall y0 : real, forall y1 : real, forall y2 : real, (x0 y0 y1 y2) -> (x0 y1 y0 y2) /\ (x0 y0 y2 y1)).
Definition term103 := exists y0 : type1624, ~ ((fun y1 : type1624 => ((forall y2 : real, forall y3 : real, forall y4 : real, (y1 y2 y3 y4) -> (y1 y3 y2 y4) /\ (y1 y2 y4 y3)) /\ (forall y2 : real, forall y3 : real, forall y4 : real, ((real_le y2 y3) /\ (real_le y3 y4)) -> y1 y2 y3 y4)) -> forall y2 : real, forall y3 : real, forall y4 : real, y1 y2 y3 y4) y0).
Definition term231 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (x0 x2 x1 x3) -> x0 x1 x2 x3.
Definition term111 (x0 : Prop) (x1 : real -> Prop) := x0 /\ (exists y0 : real, x1 y0).
Definition term227 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (x0 x2 x1 x3) \/ (~ (x0 x1 x2 x3)).
Definition term215 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (real_le x0 x1))) /\ (~ (~ (real_le x1 x2))).
Definition term10 := ~ (forall y0 : type1624, ((forall y1 : real, forall y2 : real, forall y3 : real, (y0 y1 y2 y3) -> (y0 y2 y1 y3) /\ (y0 y1 y3 y2)) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> y0 y1 y2 y3)) -> forall y1 : real, forall y2 : real, forall y3 : real, y0 y1 y2 y3).
Definition term199 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term22 (x0 : real) := forall y0 : real, (real_le x0 y0) \/ (real_le y0 x0).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term110 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term7 (x0 : Prop) := (~ x0) -> False.
Definition term216 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (real_le x0 x1)) \/ (~ (real_le x1 x2)))).
Definition term223 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := ~ (~ (x0 x1 x2 x3)).
Definition term155 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := ((~ (x0 x1 x3 x2)) \/ (x0 x3 x1 x2)) /\ ((~ (x0 x1 x3 x2)) \/ (x0 x1 x2 x3)).
Definition term140 (x0 : type1624) (x1 : real) (x2 : real) := fun y0 : real => (fun y1 : real => ~ (x0 x1 x2 y1)) y0.
Definition term173 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (~ (x0 x1 x3 x2)) \/ (x0 x1 x2 x3).
Definition term20 (x0 : real) (x1 : real) := (real_le x1 x0) \/ (real_le x0 x1).
Definition term134 (x0 : type1624) (x1 : real) := fun y0 : real => ((forall y1 : real, forall y2 : real, forall y3 : real, (~ (x0 y1 y2 y3)) \/ ((x0 y2 y1 y3) /\ (x0 y1 y3 y2))) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y3))) \/ (x0 y1 y2 y3))) /\ ((fun y1 : real => exists y2 : real, ~ (x0 x1 y1 y2)) y0).
Definition term122 (x0 : type1624) := fun y0 : real => ((forall y1 : real, forall y2 : real, forall y3 : real, (~ (x0 y1 y2 y3)) \/ ((x0 y2 y1 y3) /\ (x0 y1 y3 y2))) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y3))) \/ (x0 y1 y2 y3))) /\ ((fun y1 : real => exists y2 : real, exists y3 : real, ~ (x0 y1 y2 y3)) y0).
Definition term225 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := imp (x0 x1 x2 x3).
Definition term71 (x0 : type1624) := (forall y0 : real, forall y1 : real, forall y2 : real, (~ (x0 y0 y1 y2)) \/ ((x0 y1 y0 y2) /\ (x0 y0 y2 y1))) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (x0 y0 y1 y2)).
Definition term45 (x0 : type1624) := (forall y0 : real, forall y1 : real, forall y2 : real, (x0 y0 y1 y2) -> (x0 y1 y0 y2) /\ (x0 y0 y2 y1)) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> x0 y0 y1 y2).
Definition term74 (x0 : type1624) (x1 : real) (x2 : real) := ~ (forall y0 : real, x0 x1 x2 y0).
Definition term177 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term76 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (fun y0 : real => x0 x1 x2 y0) x3.
Definition term154 := exists y0 : type1624, exists y1 : real, exists y2 : real, exists y3 : real, ((forall y4 : real, forall y5 : real, forall y6 : real, (~ (y0 y4 y5 y6)) \/ ((y0 y5 y4 y6) /\ (y0 y4 y6 y5))) /\ (forall y4 : real, forall y5 : real, forall y6 : real, ((~ (real_le y4 y5)) \/ (~ (real_le y5 y6))) \/ (y0 y4 y5 y6))) /\ (~ (y0 y1 y2 y3)).
Definition term109 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term153 := fun y0 : type1624 => exists y1 : real, exists y2 : real, exists y3 : real, ((forall y4 : real, forall y5 : real, forall y6 : real, (~ (y0 y4 y5 y6)) \/ ((y0 y5 y4 y6) /\ (y0 y4 y6 y5))) /\ (forall y4 : real, forall y5 : real, forall y6 : real, ((~ (real_le y4 y5)) \/ (~ (real_le y5 y6))) \/ (y0 y4 y5 y6))) /\ (~ (y0 y1 y2 y3)).
Definition term52 (x0 : type1624) (x1 : real) (x2 : real) := forall y0 : real, (~ (x0 x1 x2 y0)) \/ ((x0 x2 x1 y0) /\ (x0 x1 y0 x2)).
Definition term180 (x0 : Prop) := (~ x0) -> x0.
Definition term132 (x0 : type1624) (x1 : real) (x2 : real) := ((forall y0 : real, forall y1 : real, forall y2 : real, (~ (x0 y0 y1 y2)) \/ ((x0 y1 y0 y2) /\ (x0 y0 y2 y1))) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (x0 y0 y1 y2))) /\ ((fun y0 : real => exists y1 : real, ~ (x0 x1 y0 y1)) x2).
Definition term195 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term139 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (fun y0 : real => ~ (x0 x1 x2 y0)) x3.
Definition term85 (x0 : type1624) (x1 : real) (x2 : real) := ~ ((fun y0 : real => forall y1 : real, x0 x1 y0 y1) x2).
Definition term106 := fun y0 : type1624 => ~ ((fun y1 : type1624 => ((forall y2 : real, forall y3 : real, forall y4 : real, (y1 y2 y3 y4) -> (y1 y3 y2 y4) /\ (y1 y2 y4 y3)) /\ (forall y2 : real, forall y3 : real, forall y4 : real, ((real_le y2 y3) /\ (real_le y3 y4)) -> y1 y2 y3 y4)) -> forall y2 : real, forall y3 : real, forall y4 : real, y1 y2 y3 y4) y0).
Definition term161 (x0 : type1624) := forall y0 : real, forall y1 : real, forall y2 : real, ((~ (x0 y0 y1 y2)) \/ (x0 y1 y0 y2)) /\ ((~ (x0 y0 y1 y2)) \/ (x0 y0 y2 y1)).
Definition term159 (x0 : type1624) (x1 : real) := forall y0 : real, forall y1 : real, ((~ (x0 x1 y0 y1)) \/ (x0 y0 x1 y1)) /\ ((~ (x0 x1 y0 y1)) \/ (x0 x1 y1 y0)).
Definition term69 (x0 : type1624) := forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (x0 y0 y1 y2).
Definition term67 (x0 : type1624) (x1 : real) := forall y0 : real, forall y1 : real, ((~ (real_le x1 y0)) \/ (~ (real_le y0 y1))) \/ (x0 x1 y0 y1).
Definition term56 (x0 : type1624) := forall y0 : real, forall y1 : real, forall y2 : real, (~ (x0 y0 y1 y2)) \/ ((x0 y1 y0 y2) /\ (x0 y0 y2 y1)).
Definition term54 (x0 : type1624) (x1 : real) := forall y0 : real, forall y1 : real, (~ (x0 x1 y0 y1)) \/ ((x0 y0 x1 y1) /\ (x0 x1 y1 y0)).
Definition term43 (x0 : type1624) := forall y0 : real, forall y1 : real, forall y2 : real, (x0 y0 y1 y2) -> (x0 y1 y0 y2) /\ (x0 y0 y2 y1).
Definition term41 (x0 : type1624) (x1 : real) := forall y0 : real, forall y1 : real, (x0 x1 y0 y1) -> (x0 y0 x1 y1) /\ (x0 x1 y1 y0).
Definition term36 (x0 : type1624) := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> x0 y0 y1 y2.
Definition term34 (x0 : type1624) (x1 : real) := forall y0 : real, forall y1 : real, ((real_le x1 y0) /\ (real_le y0 y1)) -> x0 x1 y0 y1.
Definition term29 (x0 : type1624) := forall y0 : real, forall y1 : real, forall y2 : real, x0 y0 y1 y2.
Definition term27 (x0 : type1624) (x1 : real) := forall y0 : real, forall y1 : real, x0 x1 y0 y1.
Definition term17 := forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0).
Definition term61 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (~ ((real_le x1 x2) /\ (real_le x2 x3))) \/ (x0 x1 x2 x3).
Definition term157 (x0 : type1624) (x1 : real) (x2 : real) := forall y0 : real, ((~ (x0 x1 x2 y0)) \/ (x0 x2 x1 y0)) /\ ((~ (x0 x1 x2 y0)) \/ (x0 x1 y0 x2)).
Definition term152 (x0 : type1624) := exists y0 : real, exists y1 : real, exists y2 : real, ((forall y3 : real, forall y4 : real, forall y5 : real, (~ (x0 y3 y4 y5)) \/ ((x0 y4 y3 y5) /\ (x0 y3 y5 y4))) /\ (forall y3 : real, forall y4 : real, forall y5 : real, ((~ (real_le y3 y4)) \/ (~ (real_le y4 y5))) \/ (x0 y3 y4 y5))) /\ (~ (x0 y0 y1 y2)).
Definition term150 (x0 : type1624) (x1 : real) := exists y0 : real, exists y1 : real, ((forall y2 : real, forall y3 : real, forall y4 : real, (~ (x0 y2 y3 y4)) \/ ((x0 y3 y2 y4) /\ (x0 y2 y4 y3))) /\ (forall y2 : real, forall y3 : real, forall y4 : real, ((~ (real_le y2 y3)) \/ (~ (real_le y3 y4))) \/ (x0 y2 y3 y4))) /\ (~ (x0 x1 y0 y1)).
Definition term95 (x0 : type1624) := exists y0 : real, exists y1 : real, exists y2 : real, ~ (x0 y0 y1 y2).
Definition term88 (x0 : type1624) (x1 : real) := exists y0 : real, exists y1 : real, ~ (x0 x1 y0 y1).
Definition term112 (x0 : Prop) (x1 : real -> Prop) := exists y0 : real, x0 /\ (x1 y0).
Definition term120 (x0 : type1624) (x1 : real) := ((forall y0 : real, forall y1 : real, forall y2 : real, (~ (x0 y0 y1 y2)) \/ ((x0 y1 y0 y2) /\ (x0 y0 y2 y1))) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (x0 y0 y1 y2))) /\ ((fun y0 : real => exists y1 : real, exists y2 : real, ~ (x0 y0 y1 y2)) x1).
Definition term144 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := ((forall y0 : real, forall y1 : real, forall y2 : real, (~ (x0 y0 y1 y2)) \/ ((x0 y1 y0 y2) /\ (x0 y0 y2 y1))) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (x0 y0 y1 y2))) /\ ((fun y0 : real => ~ (x0 x1 x2 y0)) x3).
Definition term189 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((~ (real_le x1 x2)) \/ ((~ (real_le x2 x3)) \/ (x0 x1 x2 x3))).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term49 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (~ (x0 x1 x3 x2)) \/ ((x0 x3 x1 x2) /\ (x0 x1 x2 x3)).
Definition term87 (x0 : type1624) (x1 : real) := fun y0 : real => exists y1 : real, ~ (x0 x1 y0 y1).
Definition term188 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (x0 x1 x2 x3) \/ ((~ (real_le x1 x2)) \/ (~ (real_le x2 x3))).
Definition term90 (x0 : type1624) := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, forall y3 : real, x0 y1 y2 y3) y0).
Definition term83 (x0 : type1624) (x1 : real) := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, x0 x1 y1 y2) y0).
Definition term75 (x0 : type1624) (x1 : real) (x2 : real) := exists y0 : real, ~ ((fun y1 : real => x0 x1 x2 y1) y0).
Definition term224 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := imp (~ (~ (x0 x1 x2 x3))).
Definition term221 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((x0 x1 x3 x2) \/ (~ (x0 x1 x2 x3))).
Definition term170 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (~ (real_le x1 x2)) \/ ((~ (real_le x2 x3)) \/ (x0 x1 x2 x3)).
Definition term93 (x0 : type1624) := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, forall y3 : real, x0 y1 y2 y3) y0).
Definition term86 (x0 : type1624) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, x0 x1 y1 y2) y0).
Definition term97 (x0 : type1624) := and ((forall y0 : real, forall y1 : real, forall y2 : real, (~ (x0 y0 y1 y2)) \/ ((x0 y1 y0 y2) /\ (x0 y0 y2 y1))) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (x0 y0 y1 y2))).
Definition term96 (x0 : type1624) := and ((forall y0 : real, forall y1 : real, forall y2 : real, (x0 y0 y1 y2) -> (x0 y1 y0 y2) /\ (x0 y0 y2 y1)) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> x0 y0 y1 y2)).
Definition term149 (x0 : type1624) (x1 : real) := fun y0 : real => exists y1 : real, ((forall y2 : real, forall y3 : real, forall y4 : real, (~ (x0 y2 y3 y4)) \/ ((x0 y3 y2 y4) /\ (x0 y2 y4 y3))) /\ (forall y2 : real, forall y3 : real, forall y4 : real, ((~ (real_le y2 y3)) \/ (~ (real_le y3 y4))) \/ (x0 y2 y3 y4))) /\ (~ (x0 x1 y0 y1)).
Definition term208 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (~ (~ (real_le x2 x3))) /\ (~ (x0 x1 x2 x3)).
Definition term197 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (~ (~ (real_le x1 x2))) /\ (~ (x0 x1 x2 x3)).
Definition term213 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (~ ((~ (real_le x1 x2)) \/ (~ (real_le x2 x3)))) -> x0 x1 x2 x3.
Definition term158 (x0 : type1624) (x1 : real) := fun y0 : real => forall y1 : real, ((~ (x0 x1 y0 y1)) \/ (x0 y0 x1 y1)) /\ ((~ (x0 x1 y0 y1)) \/ (x0 x1 y1 y0)).
Definition term53 (x0 : type1624) (x1 : real) := fun y0 : real => forall y1 : real, (~ (x0 x1 y0 y1)) \/ ((x0 y0 x1 y1) /\ (x0 x1 y1 y0)).
Definition term40 (x0 : type1624) (x1 : real) := fun y0 : real => forall y1 : real, (x0 x1 y0 y1) -> (x0 y0 x1 y1) /\ (x0 x1 y1 y0).
Definition term185 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (x0 x1 x2 x3) \/ (~ (real_le x2 x3)).
Definition term15 := (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term89 (x0 : type1624) := ~ (forall y0 : real, forall y1 : real, forall y2 : real, x0 y0 y1 y2).
Definition term82 (x0 : type1624) (x1 : real) := ~ (forall y0 : real, forall y1 : real, x0 x1 y0 y1).
Definition term16 := ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term104 (x0 : type1624) := (fun y0 : type1624 => ((forall y1 : real, forall y2 : real, forall y3 : real, (y0 y1 y2 y3) -> (y0 y2 y1 y3) /\ (y0 y1 y3 y2)) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> y0 y1 y2 y3)) -> forall y1 : real, forall y2 : real, forall y3 : real, y0 y1 y2 y3) x0.
Definition term191 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (~ (real_le x2 x3)) \/ ((~ (real_le x1 x2)) \/ (x0 x1 x2 x3)).
Definition term65 (x0 : type1624) (x1 : real) (x2 : real) := forall y0 : real, ((~ (real_le x1 x2)) \/ (~ (real_le x2 y0))) \/ (x0 x1 x2 y0).
Definition term79 (x0 : type1624) (x1 : real) (x2 : real) := fun y0 : real => ~ ((fun y1 : real => x0 x1 x2 y1) y0).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term13 := (((~ (forall y0 : type1624, ((forall y1 : real, forall y2 : real, forall y3 : real, (y0 y1 y2 y3) -> (y0 y2 y1 y3) /\ (y0 y1 y3 y2)) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> y0 y1 y2 y3)) -> forall y1 : real, forall y2 : real, forall y3 : real, y0 y1 y2 y3)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : type1624, ((forall y1 : real, forall y2 : real, forall y3 : real, (y0 y1 y2 y3) -> (y0 y2 y1 y3) /\ (y0 y1 y3 y2)) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> y0 y1 y2 y3)) -> forall y1 : real, forall y2 : real, forall y3 : real, y0 y1 y2 y3)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : type1624, ((forall y1 : real, forall y2 : real, forall y3 : real, (y0 y1 y2 y3) -> (y0 y2 y1 y3) /\ (y0 y1 y3 y2)) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> y0 y1 y2 y3)) -> forall y1 : real, forall y2 : real, forall y3 : real, y0 y1 y2 y3)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term228 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((~ (x0 x2 x1 x3)) \/ (x0 x1 x2 x3)).
Definition term220 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((~ (x0 x1 x3 x2)) \/ (x0 x1 x2 x3)).
Definition term46 (x0 : type1624) := imp ((forall y0 : real, forall y1 : real, forall y2 : real, (x0 y0 y1 y2) -> (x0 y1 y0 y2) /\ (x0 y0 y2 y1)) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> x0 y0 y1 y2)).
Definition term148 (x0 : type1624) (x1 : real) (x2 : real) := exists y0 : real, ((forall y1 : real, forall y2 : real, forall y3 : real, (~ (x0 y1 y2 y3)) \/ ((x0 y2 y1 y3) /\ (x0 y1 y3 y2))) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y3))) \/ (x0 y1 y2 y3))) /\ (~ (x0 x1 x2 y0)).
Definition term174 (x0 : real) (x1 : real) := (real_le x0 x1) -> ~ (real_le x0 x1).
Definition term128 (x0 : type1624) (x1 : real) := fun y0 : real => (fun y1 : real => exists y2 : real, ~ (x0 x1 y1 y2)) y0.
Definition term116 (x0 : type1624) := fun y0 : real => (fun y1 : real => exists y2 : real, exists y3 : real, ~ (x0 y1 y2 y3)) y0.
Definition term84 (x0 : type1624) (x1 : real) (x2 : real) := (fun y0 : real => forall y1 : real, x0 x1 y0 y1) x2.
Definition term211 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := imp ((real_le x2 x3) /\ (~ (x0 x1 x2 x3))).
Definition term194 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term81 (x0 : type1624) (x1 : real) (x2 : real) := exists y0 : real, ~ (x0 x1 x2 y0).
Definition term80 (x0 : type1624) (x1 : real) (x2 : real) := fun y0 : real => ~ (x0 x1 x2 y0).
Definition term37 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (x0 x1 x3 x2) -> (x0 x3 x1 x2) /\ (x0 x1 x2 x3).
Definition term217 (x0 : real) (x1 : real) (x2 : real) := imp ((real_le x0 x1) /\ (real_le x1 x2)).
Definition term190 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((x0 x1 x2 x3) \/ ((~ (real_le x1 x2)) \/ (~ (real_le x2 x3)))).
Definition term107 := fun y0 : type1624 => ((forall y1 : real, forall y2 : real, forall y3 : real, (~ (y0 y1 y2 y3)) \/ ((y0 y2 y1 y3) /\ (y0 y1 y3 y2))) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y3))) \/ (y0 y1 y2 y3))) /\ (exists y1 : real, exists y2 : real, exists y3 : real, ~ (y0 y1 y2 y3)).
Definition term51 (x0 : type1624) (x1 : real) (x2 : real) := fun y0 : real => (~ (x0 x1 x2 y0)) \/ ((x0 x2 x1 y0) /\ (x0 x1 y0 x2)).
Definition term66 (x0 : type1624) (x1 : real) := fun y0 : real => forall y1 : real, ((~ (real_le x1 y0)) \/ (~ (real_le y0 y1))) \/ (x0 x1 y0 y1).
Definition term33 (x0 : type1624) (x1 : real) := fun y0 : real => forall y1 : real, ((real_le x1 y0) /\ (real_le y0 y1)) -> x0 x1 y0 y1.
Definition term23 := fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0).
Definition term73 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term162 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) x0.
Definition term156 (x0 : type1624) (x1 : real) (x2 : real) := fun y0 : real => ((~ (x0 x1 x2 y0)) \/ (x0 x2 x1 y0)) /\ ((~ (x0 x1 x2 y0)) \/ (x0 x1 y0 x2)).
Definition term98 (x0 : type1624) := ((forall y0 : real, forall y1 : real, forall y2 : real, (x0 y0 y1 y2) -> (x0 y1 y0 y2) /\ (x0 y0 y2 y1)) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> x0 y0 y1 y2)) /\ (~ (forall y0 : real, forall y1 : real, forall y2 : real, x0 y0 y1 y2)).
Definition term60 (x0 : real) (x1 : real) (x2 : real) := or ((~ (real_le x0 x1)) \/ (~ (real_le x1 x2))).
Definition term212 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := ((real_le x3 x1) /\ (~ (x0 x2 x3 x1))) -> ~ (real_le x2 x3).
Definition term205 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := ((real_le x1 x2) /\ (~ (x0 x1 x2 x3))) -> ~ (real_le x2 x3).
Definition term141 (x0 : type1624) (x1 : real) (x2 : real) := exists y0 : real, (fun y1 : real => ~ (x0 x1 x2 y1)) y0.
Definition term9 := (~ (forall y0 : type1624, ((forall y1 : real, forall y2 : real, forall y3 : real, (y0 y1 y2 y3) -> (y0 y2 y1 y3) /\ (y0 y1 y3 y2)) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> y0 y1 y2 y3)) -> forall y1 : real, forall y2 : real, forall y3 : real, y0 y1 y2 y3)) -> False.
Definition term232 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (x0 x1 x2 x3) -> False.
Definition term38 (x0 : type1624) (x1 : real) (x2 : real) := fun y0 : real => (x0 x1 x2 y0) -> (x0 x2 x1 y0) /\ (x0 x1 y0 x2).
Definition term21 (x0 : real) := fun y0 : real => (real_le x0 y0) \/ (real_le y0 x0).
Definition term176 (x0 : real) (x1 : real) := @eq Prop ((real_le x1 x0) \/ (real_le x0 x1)).
Definition term182 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (~ (x0 x2 x1 x3)) -> ~ (x0 x1 x2 x3).
Definition term137 (x0 : type1624) (x1 : real) (x2 : real) := ((forall y0 : real, forall y1 : real, forall y2 : real, (~ (x0 y0 y1 y2)) \/ ((x0 y1 y0 y2) /\ (x0 y0 y2 y1))) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (x0 y0 y1 y2))) /\ (exists y0 : real, (fun y1 : real => ~ (x0 x1 x2 y1)) y0).
Definition term125 (x0 : type1624) (x1 : real) := ((forall y0 : real, forall y1 : real, forall y2 : real, (~ (x0 y0 y1 y2)) \/ ((x0 y1 y0 y2) /\ (x0 y0 y2 y1))) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (x0 y0 y1 y2))) /\ (exists y0 : real, (fun y1 : real => exists y2 : real, ~ (x0 x1 y1 y2)) y0).
Definition term113 (x0 : type1624) := ((forall y0 : real, forall y1 : real, forall y2 : real, (~ (x0 y0 y1 y2)) \/ ((x0 y1 y0 y2) /\ (x0 y0 y2 y1))) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (x0 y0 y1 y2))) /\ (exists y0 : real, (fun y1 : real => exists y2 : real, exists y3 : real, ~ (x0 y1 y2 y3)) y0).
Definition term143 (x0 : type1624) (x1 : real) (x2 : real) := @eq Prop (((forall y0 : real, forall y1 : real, forall y2 : real, (~ (x0 y0 y1 y2)) \/ ((x0 y1 y0 y2) /\ (x0 y0 y2 y1))) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (x0 y0 y1 y2))) /\ (exists y0 : real, ~ (x0 x1 x2 y0))).
Definition term142 (x0 : type1624) (x1 : real) (x2 : real) := @eq Prop (((forall y0 : real, forall y1 : real, forall y2 : real, (~ (x0 y0 y1 y2)) \/ ((x0 y1 y0 y2) /\ (x0 y0 y2 y1))) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (x0 y0 y1 y2))) /\ (exists y0 : real, (fun y1 : real => ~ (x0 x1 x2 y1)) y0)).
Definition term131 (x0 : type1624) (x1 : real) := @eq Prop (((forall y0 : real, forall y1 : real, forall y2 : real, (~ (x0 y0 y1 y2)) \/ ((x0 y1 y0 y2) /\ (x0 y0 y2 y1))) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (x0 y0 y1 y2))) /\ (exists y0 : real, exists y1 : real, ~ (x0 x1 y0 y1))).
Definition term130 (x0 : type1624) (x1 : real) := @eq Prop (((forall y0 : real, forall y1 : real, forall y2 : real, (~ (x0 y0 y1 y2)) \/ ((x0 y1 y0 y2) /\ (x0 y0 y2 y1))) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (x0 y0 y1 y2))) /\ (exists y0 : real, (fun y1 : real => exists y2 : real, ~ (x0 x1 y1 y2)) y0)).
Definition term119 (x0 : type1624) := @eq Prop (((forall y0 : real, forall y1 : real, forall y2 : real, (~ (x0 y0 y1 y2)) \/ ((x0 y1 y0 y2) /\ (x0 y0 y2 y1))) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (x0 y0 y1 y2))) /\ (exists y0 : real, exists y1 : real, exists y2 : real, ~ (x0 y0 y1 y2))).
Definition term118 (x0 : type1624) := @eq Prop (((forall y0 : real, forall y1 : real, forall y2 : real, (~ (x0 y0 y1 y2)) \/ ((x0 y1 y0 y2) /\ (x0 y0 y2 y1))) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (x0 y0 y1 y2))) /\ (exists y0 : real, (fun y1 : real => exists y2 : real, exists y3 : real, ~ (x0 y1 y2 y3)) y0)).
Definition term186 (x0 : real) (x1 : real) := or (~ (real_le x0 x1)).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term202 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (real_le x1 x2) /\ (~ (x0 x1 x2 x3)).
Definition term200 (x0 : real) (x1 : real) := and (~ (~ (real_le x0 x1))).
Definition term8 := forall y0 : type1624, ((forall y1 : real, forall y2 : real, forall y3 : real, (y0 y1 y2 y3) -> (y0 y2 y1 y3) /\ (y0 y1 y3 y2)) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> y0 y1 y2 y3)) -> forall y1 : real, forall y2 : real, forall y3 : real, y0 y1 y2 y3.
Definition term230 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (~ (~ (x0 x2 x1 x3))) -> x0 x1 x2 x3.
Definition term222 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (~ (~ (x0 x1 x3 x2))) -> x0 x1 x2 x3.
Definition term123 (x0 : type1624) := fun y0 : real => ((forall y1 : real, forall y2 : real, forall y3 : real, (~ (x0 y1 y2 y3)) \/ ((x0 y2 y1 y3) /\ (x0 y1 y3 y2))) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y3))) \/ (x0 y1 y2 y3))) /\ (exists y1 : real, exists y2 : real, ~ (x0 y0 y1 y2)).
Definition term172 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (~ (x0 x2 x1 x3)) \/ (x0 x1 x2 x3).
Definition term39 (x0 : type1624) (x1 : real) (x2 : real) := forall y0 : real, (x0 x1 x2 y0) -> (x0 x2 x1 y0) /\ (x0 x1 y0 x2).
Definition term183 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (~ (x0 x1 x3 x2)) -> ~ (x0 x1 x2 x3).
Definition term121 (x0 : type1624) (x1 : real) := ((forall y0 : real, forall y1 : real, forall y2 : real, (~ (x0 y0 y1 y2)) \/ ((x0 y1 y0 y2) /\ (x0 y0 y2 y1))) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (x0 y0 y1 y2))) /\ (exists y0 : real, exists y1 : real, ~ (x0 x1 y0 y1)).
Definition term99 (x0 : type1624) := ((forall y0 : real, forall y1 : real, forall y2 : real, (~ (x0 y0 y1 y2)) \/ ((x0 y1 y0 y2) /\ (x0 y0 y2 y1))) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (x0 y0 y1 y2))) /\ (exists y0 : real, exists y1 : real, exists y2 : real, ~ (x0 y0 y1 y2)).
Definition term168 (x0 : type1624) (x1 : real) (x2 : real) := (fun y0 : real => forall y1 : real, ((~ (real_le x1 y0)) \/ (~ (real_le y0 y1))) \/ (x0 x1 y0 y1)) x2.
Definition term165 (x0 : type1624) (x1 : real) (x2 : real) := (fun y0 : real => forall y1 : real, ((~ (x0 x1 y0 y1)) \/ (x0 y0 x1 y1)) /\ ((~ (x0 x1 y0 y1)) \/ (x0 x1 y1 y0))) x2.
Definition term133 (x0 : type1624) (x1 : real) (x2 : real) := ((forall y0 : real, forall y1 : real, forall y2 : real, (~ (x0 y0 y1 y2)) \/ ((x0 y1 y0 y2) /\ (x0 y0 y2 y1))) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (x0 y0 y1 y2))) /\ (exists y0 : real, ~ (x0 x1 x2 y0)).
Definition term193 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (~ (real_le x1 x2)) \/ (x0 x1 x2 x3).
Definition term147 (x0 : type1624) (x1 : real) (x2 : real) := fun y0 : real => ((forall y1 : real, forall y2 : real, forall y3 : real, (~ (x0 y1 y2 y3)) \/ ((x0 y2 y1 y3) /\ (x0 y1 y3 y2))) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y3))) \/ (x0 y1 y2 y3))) /\ (~ (x0 x1 x2 y0)).
Definition term160 (x0 : type1624) := fun y0 : real => forall y1 : real, forall y2 : real, ((~ (x0 y0 y1 y2)) \/ (x0 y1 y0 y2)) /\ ((~ (x0 y0 y1 y2)) \/ (x0 y0 y2 y1)).
Definition term68 (x0 : type1624) := fun y0 : real => forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (x0 y0 y1 y2).
Definition term55 (x0 : type1624) := fun y0 : real => forall y1 : real, forall y2 : real, (~ (x0 y0 y1 y2)) \/ ((x0 y1 y0 y2) /\ (x0 y0 y2 y1)).
Definition term42 (x0 : type1624) := fun y0 : real => forall y1 : real, forall y2 : real, (x0 y0 y1 y2) -> (x0 y1 y0 y2) /\ (x0 y0 y2 y1).
Definition term35 (x0 : type1624) := fun y0 : real => forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> x0 y0 y1 y2.
Definition term28 (x0 : type1624) := fun y0 : real => forall y1 : real, forall y2 : real, x0 y0 y1 y2.
Definition term92 (x0 : type1624) (x1 : real) := ~ ((fun y0 : real => forall y1 : real, forall y2 : real, x0 y0 y1 y2) x1).
Definition term151 (x0 : type1624) := fun y0 : real => exists y1 : real, exists y2 : real, ((forall y3 : real, forall y4 : real, forall y5 : real, (~ (x0 y3 y4 y5)) \/ ((x0 y4 y3 y5) /\ (x0 y3 y5 y4))) /\ (forall y3 : real, forall y4 : real, forall y5 : real, ((~ (real_le y3 y4)) \/ (~ (real_le y4 y5))) \/ (x0 y3 y4 y5))) /\ (~ (x0 y0 y1 y2)).
Definition term94 (x0 : type1624) := fun y0 : real => exists y1 : real, exists y2 : real, ~ (x0 y0 y1 y2).
Definition term169 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (fun y0 : real => ((~ (real_le x1 x2)) \/ (~ (real_le x2 y0))) \/ (x0 x1 x2 y0)) x3.
Definition term187 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (~ (real_le x1 x2)) \/ ((x0 x1 x2 x3) \/ (~ (real_le x2 x3))).
Definition term25 (x0 : type1624) (x1 : real) (x2 : real) := forall y0 : real, x0 x1 x2 y0.
Definition term78 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := ~ (x0 x1 x2 x3).
Definition term171 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term218 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (~ (x0 x1 x2 x3)) -> x0 x1 x2 x3.
Definition term184 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (~ (real_le x2 x3)) \/ (x0 x1 x2 x3).
Definition term214 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (real_le x0 x1)) \/ (~ (real_le x1 x2))).
Definition term19 := (~ (forall y0 : type1624, ((forall y1 : real, forall y2 : real, forall y3 : real, (y0 y1 y2 y3) -> (y0 y2 y1 y3) /\ (y0 y1 y3 y2)) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> y0 y1 y2 y3)) -> forall y1 : real, forall y2 : real, forall y3 : real, y0 y1 y2 y3)) -> ~ (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)).
Definition term24 (x0 : type1624) (x1 : real) (x2 : real) := fun y0 : real => x0 x1 x2 y0.
Definition term201 (x0 : real) (x1 : real) := and (real_le x0 x1).
Definition term229 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((x0 x2 x1 x3) \/ (~ (x0 x1 x2 x3))).
Definition term136 (x0 : type1624) (x1 : real) := exists y0 : real, ((forall y1 : real, forall y2 : real, forall y3 : real, (~ (x0 y1 y2 y3)) \/ ((x0 y2 y1 y3) /\ (x0 y1 y3 y2))) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y3))) \/ (x0 y1 y2 y3))) /\ (exists y1 : real, ~ (x0 x1 y0 y1)).
Definition term124 (x0 : type1624) := exists y0 : real, ((forall y1 : real, forall y2 : real, forall y3 : real, (~ (x0 y1 y2 y3)) \/ ((x0 y2 y1 y3) /\ (x0 y1 y3 y2))) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y3))) \/ (x0 y1 y2 y3))) /\ (exists y1 : real, exists y2 : real, ~ (x0 y0 y1 y2)).
Definition term63 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x1) /\ (real_le x1 x2).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term226 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (x0 x1 x3 x2) -> x0 x1 x2 x3.
Definition term167 (x0 : type1624) (x1 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (x0 y0 y1 y2)) x1.
Definition term164 (x0 : type1624) (x1 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((~ (x0 y0 y1 y2)) \/ (x0 y1 y0 y2)) /\ ((~ (x0 y0 y1 y2)) \/ (x0 y0 y2 y1))) x1.
Definition term91 (x0 : type1624) (x1 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, x0 y0 y1 y2) x1.
Definition term108 := exists y0 : type1624, ((forall y1 : real, forall y2 : real, forall y3 : real, (~ (y0 y1 y2 y3)) \/ ((y0 y2 y1 y3) /\ (y0 y1 y3 y2))) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y3))) \/ (y0 y1 y2 y3))) /\ (exists y1 : real, exists y2 : real, exists y3 : real, ~ (y0 y1 y2 y3)).
Definition term26 (x0 : type1624) (x1 : real) := fun y0 : real => forall y1 : real, x0 x1 y0 y1.
Definition term102 (x0 : type1013) := exists y0 : type1624, ~ (x0 y0).
Definition term135 (x0 : type1624) (x1 : real) := fun y0 : real => ((forall y1 : real, forall y2 : real, forall y3 : real, (~ (x0 y1 y2 y3)) \/ ((x0 y2 y1 y3) /\ (x0 y1 y3 y2))) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((~ (real_le y1 y2)) \/ (~ (real_le y2 y3))) \/ (x0 y1 y2 y3))) /\ (exists y1 : real, ~ (x0 x1 y0 y1)).
Definition term64 (x0 : type1624) (x1 : real) (x2 : real) := fun y0 : real => ((~ (real_le x1 x2)) \/ (~ (real_le x2 y0))) \/ (x0 x1 x2 y0).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term12 := ((~ (forall y0 : type1624, ((forall y1 : real, forall y2 : real, forall y3 : real, (y0 y1 y2 y3) -> (y0 y2 y1 y3) /\ (y0 y1 y3 y2)) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> y0 y1 y2 y3)) -> forall y1 : real, forall y2 : real, forall y3 : real, y0 y1 y2 y3)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : type1624, ((forall y1 : real, forall y2 : real, forall y3 : real, (y0 y1 y2 y3) -> (y0 y2 y1 y3) /\ (y0 y1 y3 y2)) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> y0 y1 y2 y3)) -> forall y1 : real, forall y2 : real, forall y3 : real, y0 y1 y2 y3)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term47 (x0 : type1624) := ((forall y0 : real, forall y1 : real, forall y2 : real, (x0 y0 y1 y2) -> (x0 y1 y0 y2) /\ (x0 y0 y2 y1)) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> x0 y0 y1 y2)) -> forall y0 : real, forall y1 : real, forall y2 : real, x0 y0 y1 y2.
Definition term48 := fun y0 : type1624 => ((forall y1 : real, forall y2 : real, forall y3 : real, (y0 y1 y2 y3) -> (y0 y2 y1 y3) /\ (y0 y1 y3 y2)) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> y0 y1 y2 y3)) -> forall y1 : real, forall y2 : real, forall y3 : real, y0 y1 y2 y3.
Definition term181 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (x0 x1 x2 x3) -> ~ (x0 x1 x2 x3).
Definition term62 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := ((~ (real_le x1 x2)) \/ (~ (real_le x2 x3))) \/ (x0 x1 x2 x3).
Definition term14 := (((~ (forall y0 : type1624, ((forall y1 : real, forall y2 : real, forall y3 : real, (y0 y1 y2 y3) -> (y0 y2 y1 y3) /\ (y0 y1 y3 y2)) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> y0 y1 y2 y3)) -> forall y1 : real, forall y2 : real, forall y3 : real, y0 y1 y2 y3)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : type1624, ((forall y1 : real, forall y2 : real, forall y3 : real, (y0 y1 y2 y3) -> (y0 y2 y1 y3) /\ (y0 y1 y3 y2)) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> y0 y1 y2 y3)) -> forall y1 : real, forall y2 : real, forall y3 : real, y0 y1 y2 y3)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> ((~ (forall y0 : type1624, ((forall y1 : real, forall y2 : real, forall y3 : real, (y0 y1 y2 y3) -> (y0 y2 y1 y3) /\ (y0 y1 y3 y2)) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> y0 y1 y2 y3)) -> forall y1 : real, forall y2 : real, forall y3 : real, y0 y1 y2 y3)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False) -> (~ (forall y0 : type1624, ((forall y1 : real, forall y2 : real, forall y3 : real, (y0 y1 y2 y3) -> (y0 y2 y1 y3) /\ (y0 y1 y3 y2)) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> y0 y1 y2 y3)) -> forall y1 : real, forall y2 : real, forall y3 : real, y0 y1 y2 y3)) -> (forall y0 : real, forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) -> False.
Definition term105 (x0 : type1624) := ~ ((fun y0 : type1624 => ((forall y1 : real, forall y2 : real, forall y3 : real, (y0 y1 y2 y3) -> (y0 y2 y1 y3) /\ (y0 y1 y3 y2)) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> y0 y1 y2 y3)) -> forall y1 : real, forall y2 : real, forall y3 : real, y0 y1 y2 y3) x0).
Definition term210 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := imp (~ ((~ (real_le x2 x3)) \/ (x0 x1 x2 x3))).
Definition term203 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := imp (~ ((~ (real_le x1 x2)) \/ (x0 x1 x2 x3))).
Definition term57 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_le x0 x1) /\ (real_le x1 x2)).
Definition term32 (x0 : type1624) (x1 : real) (x2 : real) := forall y0 : real, ((real_le x1 x2) /\ (real_le x2 y0)) -> x0 x1 x2 y0.
Definition term166 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (fun y0 : real => ((~ (x0 x1 x2 y0)) \/ (x0 x2 x1 y0)) /\ ((~ (x0 x1 x2 y0)) \/ (x0 x1 y0 x2))) x3.
Definition term127 (x0 : type1624) (x1 : real) (x2 : real) := (fun y0 : real => exists y1 : real, ~ (x0 x1 y0 y1)) x2.
Definition term50 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (x0 x3 x1 x2) /\ (x0 x1 x2 x3).
Definition term100 (x0 : type1624) := ~ (((forall y0 : real, forall y1 : real, forall y2 : real, (x0 y0 y1 y2) -> (x0 y1 y0 y2) /\ (x0 y0 y2 y1)) /\ (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> x0 y0 y1 y2)) -> forall y0 : real, forall y1 : real, forall y2 : real, x0 y0 y1 y2).
Definition term178 (x0 : real) (x1 : real) := (~ (real_le x1 x0)) -> real_le x0 x1.
Definition term206 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (~ ((~ (real_le x3 x1)) \/ (x0 x2 x3 x1))) -> ~ (real_le x2 x3).
Definition term192 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (~ ((~ (real_le x1 x2)) \/ (x0 x1 x2 x3))) -> ~ (real_le x2 x3).
Definition term219 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := (x0 x1 x3 x2) \/ (~ (x0 x1 x2 x3)).
Definition term163 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) \/ (real_le y0 x0)) x1.
Definition term18 := imp (~ (forall y0 : type1624, ((forall y1 : real, forall y2 : real, forall y3 : real, (y0 y1 y2 y3) -> (y0 y2 y1 y3) /\ (y0 y1 y3 y2)) /\ (forall y1 : real, forall y2 : real, forall y3 : real, ((real_le y1 y2) /\ (real_le y2 y3)) -> y0 y1 y2 y3)) -> forall y1 : real, forall y2 : real, forall y3 : real, y0 y1 y2 y3)).
Definition term175 (x0 : Prop) := x0 -> ~ x0.
Definition term204 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := imp ((real_le x1 x2) /\ (~ (x0 x1 x2 x3))).
Definition term58 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x0 x1)) \/ (~ (real_le x1 x2)).
Definition term129 (x0 : type1624) (x1 : real) := exists y0 : real, (fun y1 : real => exists y2 : real, ~ (x0 x1 y1 y2)) y0.
Definition term117 (x0 : type1624) := exists y0 : real, (fun y1 : real => exists y2 : real, exists y3 : real, ~ (x0 y1 y2 y3)) y0.
Definition term207 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := ~ ((~ (real_le x2 x3)) \/ (x0 x1 x2 x3)).
Definition term196 (x0 : type1624) (x1 : real) (x2 : real) (x3 : real) := ~ ((~ (real_le x1 x2)) \/ (x0 x1 x2 x3)).
