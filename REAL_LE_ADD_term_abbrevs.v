Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term109 (x0 : real) := ~ ((real_add x0 (real_of_num (NUMERAL 0))) = x0).
Definition term147 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp (~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3))))).
Definition term50 (x0 : real -> Prop) := ~ (all x0).
Definition term26 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x2) -> real_le (real_add x1 x0) (real_add x1 x2).
Definition term174 := (~ False) -> False.
Definition term21 := imp (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2).
Definition term134 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ (~ (real_le x0 x1))))) -> real_le x2 x3.
Definition term67 (x0 : real) (x1 : real) (x2 : real) := or (~ ((real_le x0 x1) /\ (real_le x1 x2))).
Definition term117 (x0 : Prop) := ~ (~ x0).
Definition term122 := real_of_num (NUMERAL 0).
Definition term93 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x1 x0)) \/ ((~ (real_le x0 x2)) \/ (real_le x1 x2)).
Definition term25 := (~ (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_add y0 y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> ~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2)).
Definition term46 (x0 : real) (x1 : real) := ~ (((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1)) -> real_le (real_of_num (NUMERAL 0)) (real_add x0 x1)).
Definition term171 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 (real_add x0 x1))) -> real_le (real_of_num (NUMERAL 0)) (real_add x0 x1).
Definition term88 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((~ (real_le x1 x0)) \/ (~ (real_le x0 y0))) \/ (real_le x1 y0)) x2.
Definition term131 (x0 : real) (x1 : real) (x2 : real) := (~ (x2 = x0)) \/ (~ (real_le x1 x2)).
Definition term165 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (real_le x0 x1))) /\ (~ (~ (real_le x1 x2))).
Definition term144 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (x2 = x0))) /\ (~ (~ (real_le x1 x2))).
Definition term118 (x0 : real) (x1 : real) := ~ (~ (real_le x0 x1)).
Definition term23 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> ~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2)).
Definition term33 := fun y0 : real => (real_add y0 (real_of_num (NUMERAL 0))) = y0.
Definition term78 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x0 x2)) \/ (real_le (real_add x1 x0) (real_add x1 x2)).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term7 (x0 : Prop) := (~ x0) -> False.
Definition term168 (x0 : real) (x1 : real) (x2 : real) := imp (~ ((~ (real_le x0 x1)) \/ (~ (real_le x1 x2)))).
Definition term52 (x0 : real) := ~ (forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_of_num (NUMERAL 0)) (real_add x0 y0)).
Definition term124 (x0 : real) (x1 : real) := (~ (real_le (real_add x0 (real_of_num (NUMERAL 0))) (real_add x0 x1))) -> real_le (real_add x0 (real_of_num (NUMERAL 0))) (real_add x0 x1).
Definition term55 (x0 : real) (x1 : real) := ~ ((fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_of_num (NUMERAL 0)) (real_add x0 y0)) x1).
Definition term115 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term155 (x0 : real) (x1 : real) := ~ (real_le x0 (real_add x0 x1)).
Definition term48 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1).
Definition term111 (x0 : real) (x1 : real) := ~ ((real_add x0 x1) = (real_add x0 x1)).
Definition term81 (x0 : real) (x1 : real) := forall y0 : real, (~ (real_le x0 y0)) \/ (real_le (real_add x1 x0) (real_add x1 y0)).
Definition term113 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (real_le x0 x2)) \/ (real_le (real_add x1 x0) (real_add x1 x2))).
Definition term70 (x0 : real) (x1 : real) (x2 : real) := ((~ (real_le x1 x0)) \/ (~ (real_le x0 x2))) \/ (real_le x1 x2).
Definition term107 (x0 : Prop) := (~ x0) -> x0.
Definition term32 (x0 : real) := real_add x0 (real_of_num (NUMERAL 0)).
Definition term95 (x0 : real) (x1 : real) := ~ (real_le (real_of_num (NUMERAL 0)) (real_add x0 x1)).
Definition term43 (x0 : real) := fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_of_num (NUMERAL 0)) (real_add x0 y0).
Definition term137 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term106 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) x0).
Definition term161 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((~ (real_le x1 x0)) \/ ((~ (real_le x0 x2)) \/ (real_le x1 x2))).
Definition term80 (x0 : real) (x1 : real) := fun y0 : real => (~ (real_le x0 y0)) \/ (real_le (real_add x1 x0) (real_add x1 y0)).
Definition term22 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2)) -> False.
Definition term85 := forall y0 : real, forall y1 : real, forall y2 : real, (~ (real_le y1 y2)) \/ (real_le (real_add y0 y1) (real_add y0 y2)).
Definition term83 (x0 : real) := forall y0 : real, forall y1 : real, (~ (real_le y0 y1)) \/ (real_le (real_add x0 y0) (real_add x0 y1)).
Definition term77 := forall y0 : real, forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (real_le y0 y2).
Definition term75 (x0 : real) := forall y0 : real, forall y1 : real, ((~ (real_le x0 y0)) \/ (~ (real_le y0 y1))) \/ (real_le x0 y1).
Definition term41 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2.
Definition term39 (x0 : real) := forall y0 : real, forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1.
Definition term30 (x0 : real) := forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (real_add x0 y0) (real_add x0 y1).
Definition term17 := forall y0 : real, forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2).
Definition term8 := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_add y0 y1).
Definition term162 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((real_le x0 x2) \/ ((~ (real_le x0 x1)) \/ (~ (real_le x1 x2)))).
Definition term64 := exists y0 : real, exists y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) /\ (~ (real_le (real_of_num (NUMERAL 0)) (real_add y0 y1))).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term35 (x0 : real) (x1 : real) (x2 : real) := ((real_le x1 x0) /\ (real_le x0 x2)) -> real_le x1 x2.
Definition term105 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) -> real_le (real_of_num (NUMERAL 0)) x0.
Definition term44 (x0 : real) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_of_num (NUMERAL 0)) (real_add x0 y0).
Definition term125 (x0 : real) (x1 : real) := ~ (real_le (real_add x0 (real_of_num (NUMERAL 0))) (real_add x0 x1)).
Definition term59 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_of_num (NUMERAL 0)) (real_add y1 y2)) y0).
Definition term53 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_add x0 y1)) y0).
Definition term148 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := imp ((x2 = x0) /\ ((x3 = x1) /\ (real_le x2 x3))).
Definition term172 (x0 : real) (x1 : real) := (~ (real_le (real_of_num (NUMERAL 0)) (real_add x0 x1))) -> real_le (real_of_num (NUMERAL 0)) (real_add x0 x1).
Definition term62 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le (real_of_num (NUMERAL 0)) y2)) -> real_le (real_of_num (NUMERAL 0)) (real_add y1 y2)) y0).
Definition term63 := fun y0 : real => exists y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) /\ (~ (real_le (real_of_num (NUMERAL 0)) (real_add y0 y1))).
Definition term27 (x0 : real) (x1 : real) := fun y0 : real => (real_le x0 y0) -> real_le (real_add x1 x0) (real_add x1 y0).
Definition term82 (x0 : real) := fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) \/ (real_le (real_add x0 y0) (real_add x0 y1)).
Definition term45 := fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_add y0 y1).
Definition term29 (x0 : real) := fun y0 : real => forall y1 : real, (real_le y0 y1) -> real_le (real_add x0 y0) (real_add x0 y1).
Definition term15 := (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2)) -> False.
Definition term102 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x2 = x0) -> (~ (x3 = x1)) \/ ((real_le x0 x1) \/ (~ (real_le x2 x3))).
Definition term170 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 (real_add x0 x1)).
Definition term127 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term129 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x2 = x0)) \/ ((real_le x0 x1) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3)))).
Definition term14 := (((~ (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_add y0 y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2)) -> False) -> (~ (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_add y0 y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2)) -> False) -> ((~ (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_add y0 y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2)) -> False) -> (~ (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_add y0 y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2)) -> False.
Definition term54 (x0 : real) (x1 : real) := (fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_of_num (NUMERAL 0)) (real_add x0 y0)) x1.
Definition term16 := ~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2)).
Definition term10 := ~ (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_add y0 y1)).
Definition term12 := ((~ (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_add y0 y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2)) -> False) -> (~ (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_add y0 y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2)) -> False.
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term101 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x3 = x1)) \/ ((real_le x0 x1) \/ (~ (real_le x2 x3))).
Definition term97 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_le x2 x3) = (real_le x0 x1)) -> (real_le x0 x1) \/ (~ (real_le x2 x3)).
Definition term133 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((real_le x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3))))).
Definition term126 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_le x0 x1) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3))).
Definition term136 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term69 (x0 : real) (x1 : real) (x2 : real) := (~ ((real_le x1 x0) /\ (real_le x0 x2))) \/ (real_le x1 x2).
Definition term153 (x0 : real) (x1 : real) := real_le x0 (real_add x0 x1).
Definition term152 (x0 : real) (x1 : real) := (((real_add x0 (real_of_num (NUMERAL 0))) = x0) /\ (((real_add x0 x1) = (real_add x0 x1)) /\ (real_le (real_add x0 (real_of_num (NUMERAL 0))) (real_add x0 x1)))) -> real_le x0 (real_add x0 x1).
Definition term61 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_add y0 y1)) x0).
Definition term13 := (((~ (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_add y0 y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2)) -> False) -> (~ (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_add y0 y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2)) -> False) -> (~ (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_add y0 y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2)) -> False.
Definition term20 := (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> ~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2)).
Definition term112 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_add x0 x1) (real_add x0 x2)) \/ (~ (real_le x1 x2)).
Definition term150 (x0 : real) (x1 : real) := ((real_add x0 x1) = (real_add x0 x1)) /\ (real_le (real_add x0 (real_of_num (NUMERAL 0))) (real_add x0 x1)).
Definition term169 (x0 : real) (x1 : real) (x2 : real) := imp ((real_le x0 x1) /\ (real_le x1 x2)).
Definition term154 (x0 : real) (x1 : real) := (~ (real_le x0 (real_add x0 x1))) -> real_le x0 (real_add x0 x1).
Definition term74 (x0 : real) := fun y0 : real => forall y1 : real, ((~ (real_le x0 y0)) \/ (~ (real_le y0 y1))) \/ (real_le x0 y1).
Definition term38 (x0 : real) := fun y0 : real => forall y1 : real, ((real_le x0 y0) /\ (real_le y0 y1)) -> real_le x0 y1.
Definition term51 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term19 := (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2)) -> False.
Definition term60 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_add y0 y1)) x0.
Definition term58 (x0 : real) := exists y0 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (~ (real_le (real_of_num (NUMERAL 0)) (real_add x0 y0))).
Definition term138 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3)))).
Definition term68 (x0 : real) (x1 : real) (x2 : real) := or ((~ (real_le x0 x1)) \/ (~ (real_le x1 x2))).
Definition term104 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term9 := (~ (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_add y0 y1))) -> False.
Definition term173 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) (real_add x0 x1)) -> False.
Definition term149 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((x0 = x2) /\ ((x1 = x3) /\ (real_le x0 x1))) -> real_le x2 x3.
Definition term47 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1)) /\ (~ (real_le (real_of_num (NUMERAL 0)) (real_add x0 x1))).
Definition term11 := (~ (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_add y0 y1))) -> (forall y0 : real, forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2) -> (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0) -> (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2)) -> False.
Definition term79 (x0 : real) (x1 : real) (x2 : real) := real_le (real_add x1 x0) (real_add x1 x2).
Definition term158 (x0 : real) (x1 : real) := or (~ (real_le x0 x1)).
Definition term130 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_le x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3)))).
Definition term145 (x0 : real) (x1 : real) (x2 : real) := (x2 = x0) /\ (real_le x1 x2).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term151 (x0 : real) (x1 : real) := ((real_add x0 (real_of_num (NUMERAL 0))) = x0) /\ (((real_add x0 x1) = (real_add x0 x1)) /\ (real_le (real_add x0 (real_of_num (NUMERAL 0))) (real_add x0 x1))).
Definition term91 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (~ (real_le y0 y1)) \/ (real_le (real_add x0 y0) (real_add x0 y1))) x1.
Definition term87 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((~ (real_le x0 y0)) \/ (~ (real_le y0 y1))) \/ (real_le x0 y1)) x1.
Definition term166 (x0 : real) (x1 : real) := and (~ (~ (real_le x0 x1))).
Definition term141 (x0 : real) (x1 : real) := and (~ (~ (x0 = x1))).
Definition term114 (x0 : real) (x1 : real) (x2 : real) := @eq Prop ((real_le (real_add x0 x1) (real_add x0 x2)) \/ (~ (real_le x1 x2))).
Definition term57 (x0 : real) := fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (~ (real_le (real_of_num (NUMERAL 0)) (real_add x0 y0))).
Definition term163 (x0 : real) (x1 : real) (x2 : real) := (~ ((~ (real_le x1 x0)) \/ (~ (real_le x0 x2)))) -> real_le x1 x2.
Definition term49 (x0 : real) (x1 : real) := real_le (real_of_num (NUMERAL 0)) (real_add x0 x1).
Definition term121 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) x1) -> real_le (real_add x0 (real_of_num (NUMERAL 0))) (real_add x0 x1).
Definition term72 (x0 : real) (x1 : real) := fun y0 : real => ((~ (real_le x1 x0)) \/ (~ (real_le x0 y0))) \/ (real_le x1 y0).
Definition term96 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term157 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x2) \/ (~ (real_le x1 x2)).
Definition term108 (x0 : real) := (~ ((real_add x0 (real_of_num (NUMERAL 0))) = x0)) -> (real_add x0 (real_of_num (NUMERAL 0))) = x0.
Definition term28 (x0 : real) (x1 : real) := forall y0 : real, (real_le x0 y0) -> real_le (real_add x1 x0) (real_add x1 y0).
Definition term18 := imp (forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0).
Definition term116 (x0 : real) (x1 : real) (x2 : real) := (~ (~ (real_le x0 x2))) -> real_le (real_add x1 x0) (real_add x1 x2).
Definition term84 := fun y0 : real => forall y1 : real, forall y2 : real, (~ (real_le y1 y2)) \/ (real_le (real_add y0 y1) (real_add y0 y2)).
Definition term76 := fun y0 : real => forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (real_le y0 y2).
Definition term40 := fun y0 : real => forall y1 : real, forall y2 : real, ((real_le y0 y1) /\ (real_le y1 y2)) -> real_le y0 y2.
Definition term31 := fun y0 : real => forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2).
Definition term34 := forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0.
Definition term120 (x0 : real) (x1 : real) := imp (real_le x0 x1).
Definition term94 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term135 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (real_le x2 x3))).
Definition term164 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (real_le x0 x1)) \/ (~ (real_le x1 x2))).
Definition term143 (x0 : real) (x1 : real) (x2 : real) := ~ ((~ (x2 = x0)) \/ (~ (real_le x1 x2))).
Definition term37 (x0 : real) (x1 : real) := forall y0 : real, ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0.
Definition term132 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq Prop ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((real_le x0 x1) \/ (~ (real_le x2 x3))))).
Definition term142 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term167 (x0 : real) (x1 : real) := and (real_le x0 x1).
Definition term92 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (~ (real_le x0 y0)) \/ (real_le (real_add x1 x0) (real_add x1 y0))) x2.
Definition term100 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term139 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (~ (x2 = x0))) /\ (~ ((~ (x3 = x1)) \/ (~ (real_le x2 x3)))).
Definition term71 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x1) /\ (real_le x1 x2).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term56 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_add x0 y1)) y0).
Definition term99 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x3 = x1) -> (real_le x0 x1) \/ (~ (real_le x2 x3)).
Definition term146 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (x2 = x0) /\ ((x3 = x1) /\ (real_le x2 x3)).
Definition term123 (x0 : real) (x1 : real) := real_le (real_add x0 (real_of_num (NUMERAL 0))) (real_add x0 x1).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term36 (x0 : real) (x1 : real) := fun y0 : real => ((real_le x1 x0) /\ (real_le x0 y0)) -> real_le x1 y0.
Definition term159 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x0 x1)) \/ ((real_le x0 x2) \/ (~ (real_le x1 x2))).
Definition term89 (x0 : real) := (fun y0 : real => (real_add y0 (real_of_num (NUMERAL 0))) = y0) x0.
Definition term140 (x0 : real) (x1 : real) := ~ (~ (x0 = x1)).
Definition term128 (x0 : real) (x1 : real) := or (~ (x0 = x1)).
Definition term65 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_le x0 x1) /\ (real_le x1 x2)).
Definition term156 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x0 x2)) \/ (real_le x1 x2).
Definition term110 (x0 : real) (x1 : real) := (~ ((real_add x0 x1) = (real_add x0 x1))) -> (real_add x0 x1) = (real_add x0 x1).
Definition term90 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (~ (real_le y1 y2)) \/ (real_le (real_add y0 y1) (real_add y0 y2))) x0.
Definition term86 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((~ (real_le y0 y1)) \/ (~ (real_le y1 y2))) \/ (real_le y0 y2)) x0.
Definition term103 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((real_le x0 x1) \/ (~ (real_le x2 x3)))).
Definition term160 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x2) \/ ((~ (real_le x0 x1)) \/ (~ (real_le x1 x2))).
Definition term24 := imp (~ (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_add y0 y1))).
Definition term98 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_le x0 x1) \/ (~ (real_le x2 x3)).
Definition term73 (x0 : real) (x1 : real) := forall y0 : real, ((~ (real_le x1 x0)) \/ (~ (real_le x0 y0))) \/ (real_le x1 y0).
Definition term42 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1)) -> real_le (real_of_num (NUMERAL 0)) (real_add x0 x1).
Definition term66 (x0 : real) (x1 : real) (x2 : real) := (~ (real_le x0 x1)) \/ (~ (real_le x1 x2)).
Definition term119 (x0 : real) (x1 : real) := imp (~ (~ (real_le x0 x1))).