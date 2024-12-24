Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term136 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, nadd_eq (nadd_mul y0 y1) (nadd_mul y1 y0)) x0.
Definition term169 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (nadd_le x0 x1) \/ ((~ (nadd_eq x2 x0)) \/ ((~ (nadd_eq x3 x1)) \/ (~ (nadd_le x2 x3)))).
Definition term186 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := imp (~ ((~ (nadd_eq x2 x0)) \/ ((~ (nadd_eq x3 x1)) \/ (~ (nadd_le x2 x3))))).
Definition term55 (x0 : nadd -> Prop) := ~ (all x0).
Definition term194 := (~ False) -> False.
Definition term193 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_le (nadd_mul x0 x2) (nadd_mul x1 x2)) -> False.
Definition term145 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ((~ (nadd_eq x0 x2)) \/ (~ (nadd_eq x1 x3))) \/ ((~ (nadd_le x0 x1)) \/ (nadd_le x2 x3)).
Definition term85 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ~ (nadd_le (nadd_mul x0 x2) (nadd_mul x1 x2)).
Definition term87 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_le x0 x1) /\ ((fun y0 : nadd => ~ (nadd_le (nadd_mul x0 y0) (nadd_mul x1 y0))) x2).
Definition term158 (x0 : Prop) := ~ (~ x0).
Definition term109 (x0 : nadd) (x1 : nadd) (x2 : nadd) := fun y0 : nadd => ((~ (nadd_eq x0 x2)) \/ (~ (nadd_eq x1 y0))) \/ (((nadd_le x0 x1) \/ (~ (nadd_le x2 y0))) /\ ((~ (nadd_le x0 x1)) \/ (nadd_le x2 y0))).
Definition term25 := (~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y0 y1) -> nadd_le (nadd_mul y0 y2) (nadd_mul y1 y2))) -> (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_mul y0 y1) (nadd_mul y1 y0)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> ~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y1 y2) -> nadd_le (nadd_mul y0 y1) (nadd_mul y0 y2)).
Definition term80 (x0 : Prop) (x1 : nadd -> Prop) := x0 /\ (exists y0 : nadd, x1 y0).
Definition term44 := fun y0 : nadd => forall y1 : nadd, nadd_eq (nadd_mul y0 y1) (nadd_mul y1 y0).
Definition term183 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (~ (~ (nadd_eq x2 x0))) /\ (~ (~ (nadd_le x1 x2))).
Definition term118 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_le (nadd_mul x1 x0) (nadd_mul x1 x2).
Definition term23 := (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_mul y0 y1) (nadd_mul y1 y0)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> ~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y1 y2) -> nadd_le (nadd_mul y0 y1) (nadd_mul y0 y2)).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term188 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ((nadd_eq x0 x2) /\ ((nadd_eq x1 x3) /\ (nadd_le x0 x1))) -> nadd_le x2 x3.
Definition term135 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, (((~ (nadd_eq y0 y1)) \/ (~ (nadd_eq y2 y3))) \/ ((nadd_le y0 y2) \/ (~ (nadd_le y1 y3)))) /\ (((~ (nadd_eq y0 y1)) \/ (~ (nadd_eq y2 y3))) \/ ((~ (nadd_le y0 y2)) \/ (nadd_le y1 y3))).
Definition term133 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (((~ (nadd_eq x0 y0)) \/ (~ (nadd_eq y1 y2))) \/ ((nadd_le x0 y1) \/ (~ (nadd_le y0 y2)))) /\ (((~ (nadd_eq x0 y0)) \/ (~ (nadd_eq y1 y2))) \/ ((~ (nadd_le x0 y1)) \/ (nadd_le y0 y2))).
Definition term131 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, forall y1 : nadd, (((~ (nadd_eq x0 x1)) \/ (~ (nadd_eq y0 y1))) \/ ((nadd_le x0 y0) \/ (~ (nadd_le x1 y1)))) /\ (((~ (nadd_eq x0 x1)) \/ (~ (nadd_eq y0 y1))) \/ ((~ (nadd_le x0 y0)) \/ (nadd_le x1 y1))).
Definition term124 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (~ (nadd_le y1 y2)) \/ (nadd_le (nadd_mul y0 y1) (nadd_mul y0 y2)).
Definition term122 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, (~ (nadd_le y0 y1)) \/ (nadd_le (nadd_mul x0 y0) (nadd_mul x0 y1)).
Definition term116 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((~ (nadd_eq y0 y1)) \/ (~ (nadd_eq y2 y3))) \/ (((nadd_le y0 y2) \/ (~ (nadd_le y1 y3))) /\ ((~ (nadd_le y0 y2)) \/ (nadd_le y1 y3))).
Definition term114 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((~ (nadd_eq x0 y0)) \/ (~ (nadd_eq y1 y2))) \/ (((nadd_le x0 y1) \/ (~ (nadd_le y0 y2))) /\ ((~ (nadd_le x0 y1)) \/ (nadd_le y0 y2))).
Definition term112 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, forall y1 : nadd, ((~ (nadd_eq x0 x1)) \/ (~ (nadd_eq y0 y1))) \/ (((nadd_le x0 y0) \/ (~ (nadd_le x1 y1))) /\ ((~ (nadd_le x0 y0)) \/ (nadd_le x1 y1))).
Definition term50 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, (nadd_le x0 y0) -> nadd_le (nadd_mul x0 y1) (nadd_mul y0 y1).
Definition term45 := forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_mul y0 y1) (nadd_mul y1 y0).
Definition term40 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3).
Definition term38 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq y1 y2)) -> (nadd_le x0 y1) = (nadd_le y0 y2).
Definition term36 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, forall y1 : nadd, ((nadd_eq x0 x1) /\ (nadd_eq y0 y1)) -> (nadd_le x0 y0) = (nadd_le x1 y1).
Definition term30 (x0 : nadd) := forall y0 : nadd, forall y1 : nadd, (nadd_le y0 y1) -> nadd_le (nadd_mul x0 y0) (nadd_mul x0 y1).
Definition term17 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y1 y2) -> nadd_le (nadd_mul y0 y1) (nadd_mul y0 y2).
Definition term8 := forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y0 y1) -> nadd_le (nadd_mul y0 y2) (nadd_mul y1 y2).
Definition term77 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term7 (x0 : Prop) := (~ x0) -> False.
Definition term32 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ((nadd_eq x0 x2) /\ (nadd_eq x1 x3)) -> (nadd_le x0 x1) = (nadd_le x2 x3).
Definition term161 (x0 : nadd) (x1 : nadd) := imp (nadd_le x0 x1).
Definition term61 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => ~ ((fun y1 : nadd => (nadd_le x0 x1) -> nadd_le (nadd_mul x0 y1) (nadd_mul x1 y1)) y0).
Definition term162 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (~ (nadd_le (nadd_mul x1 x0) (nadd_mul x1 x2))) -> nadd_le (nadd_mul x1 x0) (nadd_mul x1 x2).
Definition term144 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => (~ (nadd_le x0 y0)) \/ (nadd_le (nadd_mul x1 x0) (nadd_mul x1 y0))) x2.
Definition term108 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (nadd_eq x0 x1) /\ (nadd_eq x2 x3).
Definition term190 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_eq (nadd_mul x1 x0) (nadd_mul x0 x1)) /\ ((nadd_eq (nadd_mul x1 x2) (nadd_mul x2 x1)) /\ (nadd_le (nadd_mul x1 x0) (nadd_mul x1 x2))).
Definition term147 (x0 : nadd) (x1 : nadd) := ~ (nadd_eq x0 x1).
Definition term156 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term82 (x0 : nadd) (x1 : nadd) := (nadd_le x0 x1) /\ (exists y0 : nadd, (fun y1 : nadd => ~ (nadd_le (nadd_mul x0 y1) (nadd_mul x1 y1))) y0).
Definition term78 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term53 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_le x0 x1) /\ (~ (nadd_le (nadd_mul x0 x2) (nadd_mul x1 x2))).
Definition term128 (x0 : nadd) (x1 : nadd) (x2 : nadd) := fun y0 : nadd => (((~ (nadd_eq x0 x2)) \/ (~ (nadd_eq x1 y0))) \/ ((nadd_le x0 x1) \/ (~ (nadd_le x2 y0)))) /\ (((~ (nadd_eq x0 x2)) \/ (~ (nadd_eq x1 y0))) \/ ((~ (nadd_le x0 x1)) \/ (nadd_le x2 y0))).
Definition term150 (x0 : Prop) := (~ x0) -> x0.
Definition term151 (x0 : nadd) (x1 : nadd) := (~ (nadd_le x0 x1)) -> nadd_le x0 x1.
Definition term106 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (~ ((nadd_eq x0 x2) /\ (nadd_eq x1 x3))) \/ ((nadd_le x0 x1) = (nadd_le x2 x3)).
Definition term176 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term100 (x0 : nadd) (x1 : nadd) := @eq Prop ((nadd_le x0 x1) /\ (exists y0 : nadd, ~ (nadd_le (nadd_mul x0 y0) (nadd_mul x1 y0)))).
Definition term99 (x0 : nadd) (x1 : nadd) := @eq Prop ((nadd_le x0 x1) /\ (exists y0 : nadd, (fun y1 : nadd => ~ (nadd_le (nadd_mul x0 y1) (nadd_mul x1 y1))) y0)).
Definition term52 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ~ ((nadd_le x0 x1) -> nadd_le (nadd_mul x0 x2) (nadd_mul x1 x2)).
Definition term170 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (~ (nadd_eq x2 x0)) \/ (~ (nadd_le x1 x2)).
Definition term22 := (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_mul y0 y1) (nadd_mul y1 y0)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y1 y2) -> nadd_le (nadd_mul y0 y1) (nadd_mul y0 y2)) -> False.
Definition term46 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_le x0 x1) -> nadd_le (nadd_mul x0 x2) (nadd_mul x1 x2).
Definition term19 := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y1 y2) -> nadd_le (nadd_mul y0 y1) (nadd_mul y0 y2)) -> False.
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term159 (x0 : nadd) (x1 : nadd) := ~ (~ (nadd_le x0 x1)).
Definition term119 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (~ (nadd_le x0 y0)) \/ (nadd_le (nadd_mul x1 x0) (nadd_mul x1 y0)).
Definition term83 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => ~ (nadd_le (nadd_mul x0 y0) (nadd_mul x1 y0)).
Definition term71 := exists y0 : nadd, ~ ((fun y1 : nadd => forall y2 : nadd, forall y3 : nadd, (nadd_le y1 y2) -> nadd_le (nadd_mul y1 y3) (nadd_mul y2 y3)) y0).
Definition term65 (x0 : nadd) := exists y0 : nadd, ~ ((fun y1 : nadd => forall y2 : nadd, (nadd_le x0 y1) -> nadd_le (nadd_mul x0 y2) (nadd_mul y1 y2)) y0).
Definition term58 (x0 : nadd) (x1 : nadd) := exists y0 : nadd, ~ ((fun y1 : nadd => (nadd_le x0 x1) -> nadd_le (nadd_mul x0 y1) (nadd_mul x1 y1)) y0).
Definition term173 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (~ ((~ (nadd_eq x0 x2)) \/ ((~ (nadd_eq x1 x3)) \/ (~ (nadd_le x0 x1))))) -> nadd_le x2 x3.
Definition term139 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, (((~ (nadd_eq x0 y0)) \/ (~ (nadd_eq y1 y2))) \/ ((nadd_le x0 y1) \/ (~ (nadd_le y0 y2)))) /\ (((~ (nadd_eq x0 y0)) \/ (~ (nadd_eq y1 y2))) \/ ((~ (nadd_le x0 y1)) \/ (nadd_le y0 y2)))) x1.
Definition term187 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := imp ((nadd_eq x2 x0) /\ ((nadd_eq x3 x1) /\ (nadd_le x2 x3))).
Definition term74 := fun y0 : nadd => ~ ((fun y1 : nadd => forall y2 : nadd, forall y3 : nadd, (nadd_le y1 y2) -> nadd_le (nadd_mul y1 y3) (nadd_mul y2 y3)) y0).
Definition term68 (x0 : nadd) := fun y0 : nadd => ~ ((fun y1 : nadd => forall y2 : nadd, (nadd_le x0 y1) -> nadd_le (nadd_mul x0 y2) (nadd_mul y1 y2)) y0).
Definition term60 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ~ ((fun y0 : nadd => (nadd_le x0 x1) -> nadd_le (nadd_mul x0 y0) (nadd_mul x1 y0)) x2).
Definition term59 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => (nadd_le x0 x1) -> nadd_le (nadd_mul x0 y0) (nadd_mul x1 y0)) x2.
Definition term69 (x0 : nadd) := fun y0 : nadd => exists y1 : nadd, (nadd_le x0 y0) /\ (~ (nadd_le (nadd_mul x0 y1) (nadd_mul y0 y1))).
Definition term43 (x0 : nadd) := forall y0 : nadd, nadd_eq (nadd_mul x0 y0) (nadd_mul y0 x0).
Definition term15 := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y1 y2) -> nadd_le (nadd_mul y0 y1) (nadd_mul y0 y2)) -> False.
Definition term126 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (nadd_le x0 x1) \/ (~ (nadd_le x2 x3)).
Definition term191 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ((nadd_eq (nadd_mul x2 x0) (nadd_mul x0 x2)) /\ ((nadd_eq (nadd_mul x2 x1) (nadd_mul x1 x2)) /\ (nadd_le (nadd_mul x2 x0) (nadd_mul x2 x1)))) -> nadd_le (nadd_mul x0 x2) (nadd_mul x1 x2).
Definition term168 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (~ (nadd_eq x2 x0)) \/ ((nadd_le x0 x1) \/ ((~ (nadd_eq x3 x1)) \/ (~ (nadd_le x2 x3)))).
Definition term84 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => ~ (nadd_le (nadd_mul x0 y0) (nadd_mul x1 y0))) x2.
Definition term14 := (((~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y0 y1) -> nadd_le (nadd_mul y0 y2) (nadd_mul y1 y2))) -> (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_mul y0 y1) (nadd_mul y1 y0)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y1 y2) -> nadd_le (nadd_mul y0 y1) (nadd_mul y0 y2)) -> False) -> (~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y0 y1) -> nadd_le (nadd_mul y0 y2) (nadd_mul y1 y2))) -> (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_mul y0 y1) (nadd_mul y1 y0)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y1 y2) -> nadd_le (nadd_mul y0 y1) (nadd_mul y0 y2)) -> False) -> ((~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y0 y1) -> nadd_le (nadd_mul y0 y2) (nadd_mul y1 y2))) -> (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_mul y0 y1) (nadd_mul y1 y0)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y1 y2) -> nadd_le (nadd_mul y0 y1) (nadd_mul y0 y2)) -> False) -> (~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y0 y1) -> nadd_le (nadd_mul y0 y2) (nadd_mul y1 y2))) -> (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_mul y0 y1) (nadd_mul y1 y0)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y1 y2) -> nadd_le (nadd_mul y0 y1) (nadd_mul y0 y2)) -> False.
Definition term42 (x0 : nadd) := fun y0 : nadd => nadd_eq (nadd_mul x0 y0) (nadd_mul y0 x0).
Definition term81 (x0 : nadd) (x1 : nadd) := exists y0 : nadd, (nadd_le x0 x1) /\ ((fun y1 : nadd => ~ (nadd_le (nadd_mul x0 y1) (nadd_mul x1 y1))) y0).
Definition term12 := ((~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y0 y1) -> nadd_le (nadd_mul y0 y2) (nadd_mul y1 y2))) -> (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_mul y0 y1) (nadd_mul y1 y0)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y1 y2) -> nadd_le (nadd_mul y0 y1) (nadd_mul y0 y2)) -> False) -> (~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y0 y1) -> nadd_le (nadd_mul y0 y2) (nadd_mul y1 y2))) -> (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_mul y0 y1) (nadd_mul y1 y0)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y1 y2) -> nadd_le (nadd_mul y0 y1) (nadd_mul y0 y2)) -> False.
Definition term90 (x0 : nadd) (x1 : nadd) := @eq Prop (exists y0 : nadd, (nadd_le x0 x1) /\ (~ (nadd_le (nadd_mul x0 y0) (nadd_mul x1 y0)))).
Definition term89 (x0 : nadd) (x1 : nadd) := @eq Prop (exists y0 : nadd, (nadd_le x0 x1) /\ ((fun y1 : nadd => ~ (nadd_le (nadd_mul x0 y1) (nadd_mul x1 y1))) y0)).
Definition term192 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (~ (nadd_le (nadd_mul x0 x2) (nadd_mul x1 x2))) -> nadd_le (nadd_mul x0 x2) (nadd_mul x1 x2).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term166 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (~ (nadd_eq x3 x1)) \/ ((nadd_le x0 x1) \/ (~ (nadd_le x2 x3))).
Definition term103 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ((nadd_le x0 x1) \/ (~ (nadd_le x2 x3))) /\ ((~ (nadd_le x0 x1)) \/ (nadd_le x2 x3)).
Definition term172 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := @eq Prop ((nadd_le x0 x1) \/ ((~ (nadd_eq x2 x0)) \/ ((~ (nadd_eq x3 x1)) \/ (~ (nadd_le x2 x3))))).
Definition term57 (x0 : nadd) (x1 : nadd) := ~ (forall y0 : nadd, (nadd_le x0 x1) -> nadd_le (nadd_mul x0 y0) (nadd_mul x1 y0)).
Definition term26 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_le x0 x2) -> nadd_le (nadd_mul x1 x0) (nadd_mul x1 x2).
Definition term153 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_le (nadd_mul x0 x1) (nadd_mul x0 x2)) \/ (~ (nadd_le x1 x2)).
Definition term142 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, (~ (nadd_le y1 y2)) \/ (nadd_le (nadd_mul y0 y1) (nadd_mul y0 y2))) x0.
Definition term138 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, (((~ (nadd_eq y0 y1)) \/ (~ (nadd_eq y2 y3))) \/ ((nadd_le y0 y2) \/ (~ (nadd_le y1 y3)))) /\ (((~ (nadd_eq y0 y1)) \/ (~ (nadd_eq y2 y3))) \/ ((~ (nadd_le y0 y2)) \/ (nadd_le y1 y3)))) x0.
Definition term72 (x0 : nadd) := (fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, (nadd_le y0 y1) -> nadd_le (nadd_mul y0 y2) (nadd_mul y1 y2)) x0.
Definition term175 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term21 := imp (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_mul y0 y1) (nadd_mul y1 y0)).
Definition term18 := imp (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)).
Definition term93 (x0 : nadd) (x1 : nadd) := exists y0 : nadd, ~ (nadd_le (nadd_mul x0 y0) (nadd_mul x1 y0)).
Definition term134 := fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, (((~ (nadd_eq y0 y1)) \/ (~ (nadd_eq y2 y3))) \/ ((nadd_le y0 y2) \/ (~ (nadd_le y1 y3)))) /\ (((~ (nadd_eq y0 y1)) \/ (~ (nadd_eq y2 y3))) \/ ((~ (nadd_le y0 y2)) \/ (nadd_le y1 y3))).
Definition term132 (x0 : nadd) := fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, (((~ (nadd_eq x0 y0)) \/ (~ (nadd_eq y1 y2))) \/ ((nadd_le x0 y1) \/ (~ (nadd_le y0 y2)))) /\ (((~ (nadd_eq x0 y0)) \/ (~ (nadd_eq y1 y2))) \/ ((~ (nadd_le x0 y1)) \/ (nadd_le y0 y2))).
Definition term123 := fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, (~ (nadd_le y1 y2)) \/ (nadd_le (nadd_mul y0 y1) (nadd_mul y0 y2)).
Definition term115 := fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((~ (nadd_eq y0 y1)) \/ (~ (nadd_eq y2 y3))) \/ (((nadd_le y0 y2) \/ (~ (nadd_le y1 y3))) /\ ((~ (nadd_le y0 y2)) \/ (nadd_le y1 y3))).
Definition term113 (x0 : nadd) := fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, ((~ (nadd_eq x0 y0)) \/ (~ (nadd_eq y1 y2))) \/ (((nadd_le x0 y1) \/ (~ (nadd_le y0 y2))) /\ ((~ (nadd_le x0 y1)) \/ (nadd_le y0 y2))).
Definition term51 := fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, (nadd_le y0 y1) -> nadd_le (nadd_mul y0 y2) (nadd_mul y1 y2).
Definition term39 := fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3).
Definition term37 (x0 : nadd) := fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, ((nadd_eq x0 y0) /\ (nadd_eq y1 y2)) -> (nadd_le x0 y1) = (nadd_le y0 y2).
Definition term31 := fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, (nadd_le y1 y2) -> nadd_le (nadd_mul y0 y1) (nadd_mul y0 y2).
Definition term165 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (~ (nadd_eq x1 x3)) \/ ((~ (nadd_le x0 x1)) \/ (nadd_le x2 x3)).
Definition term79 (x0 : Prop) (x1 : nadd -> Prop) := exists y0 : nadd, x0 /\ (x1 y0).
Definition term13 := (((~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y0 y1) -> nadd_le (nadd_mul y0 y2) (nadd_mul y1 y2))) -> (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_mul y0 y1) (nadd_mul y1 y0)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y1 y2) -> nadd_le (nadd_mul y0 y1) (nadd_mul y0 y2)) -> False) -> (~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y0 y1) -> nadd_le (nadd_mul y0 y2) (nadd_mul y1 y2))) -> (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_mul y0 y1) (nadd_mul y1 y0)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y1 y2) -> nadd_le (nadd_mul y0 y1) (nadd_mul y0 y2)) -> False) -> (~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y0 y1) -> nadd_le (nadd_mul y0 y2) (nadd_mul y1 y2))) -> (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_mul y0 y1) (nadd_mul y1 y0)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y1 y2) -> nadd_le (nadd_mul y0 y1) (nadd_mul y0 y2)) -> False.
Definition term149 (x0 : nadd) (x1 : nadd) := ~ (nadd_eq (nadd_mul x1 x0) (nadd_mul x0 x1)).
Definition term171 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := @eq Prop ((~ (nadd_eq x0 x2)) \/ ((~ (nadd_eq x1 x3)) \/ ((~ (nadd_le x0 x1)) \/ (nadd_le x2 x3)))).
Definition term129 (x0 : nadd) (x1 : nadd) (x2 : nadd) := forall y0 : nadd, (((~ (nadd_eq x0 x2)) \/ (~ (nadd_eq x1 y0))) \/ ((nadd_le x0 x1) \/ (~ (nadd_le x2 y0)))) /\ (((~ (nadd_eq x0 x2)) \/ (~ (nadd_eq x1 y0))) \/ ((~ (nadd_le x0 x1)) \/ (nadd_le x2 y0))).
Definition term181 (x0 : nadd) (x1 : nadd) := and (nadd_eq x0 x1).
Definition term101 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ~ ((nadd_eq x0 x1) /\ (nadd_eq x2 x3)).
Definition term88 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (nadd_le x0 x1) /\ ((fun y1 : nadd => ~ (nadd_le (nadd_mul x0 y1) (nadd_mul x1 y1))) y0).
Definition term164 (x0 : nadd) (x1 : nadd) := or (~ (nadd_eq x0 x1)).
Definition term140 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (fun y0 : nadd => forall y1 : nadd, (((~ (nadd_eq x0 x1)) \/ (~ (nadd_eq y0 y1))) \/ ((nadd_le x0 y0) \/ (~ (nadd_le x1 y1)))) /\ (((~ (nadd_eq x0 x1)) \/ (~ (nadd_eq y0 y1))) \/ ((~ (nadd_le x0 y0)) \/ (nadd_le x1 y1)))) x2.
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term41 (x0 : nadd) (x1 : nadd) := nadd_eq (nadd_mul x1 x0) (nadd_mul x0 x1).
Definition term95 (x0 : nadd) := fun y0 : nadd => (nadd_le x0 y0) /\ (exists y1 : nadd, ~ (nadd_le (nadd_mul x0 y1) (nadd_mul y0 y1))).
Definition term177 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ~ ((~ (nadd_eq x2 x0)) \/ ((~ (nadd_eq x3 x1)) \/ (~ (nadd_le x2 x3)))).
Definition term63 (x0 : nadd) (x1 : nadd) := exists y0 : nadd, (nadd_le x0 x1) /\ (~ (nadd_le (nadd_mul x0 y0) (nadd_mul x1 y0))).
Definition term105 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := or ((~ (nadd_eq x0 x1)) \/ (~ (nadd_eq x2 x3))).
Definition term9 := (~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y0 y1) -> nadd_le (nadd_mul y0 y2) (nadd_mul y1 y2))) -> False.
Definition term146 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (~ (nadd_eq x0 x2)) \/ ((~ (nadd_eq x1 x3)) \/ ((~ (nadd_le x0 x1)) \/ (nadd_le x2 x3))).
Definition term97 := fun y0 : nadd => exists y1 : nadd, (nadd_le y0 y1) /\ (exists y2 : nadd, ~ (nadd_le (nadd_mul y0 y2) (nadd_mul y1 y2))).
Definition term189 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_eq (nadd_mul x1 x2) (nadd_mul x2 x1)) /\ (nadd_le (nadd_mul x1 x0) (nadd_mul x1 x2)).
Definition term11 := (~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y0 y1) -> nadd_le (nadd_mul y0 y2) (nadd_mul y1 y2))) -> (forall y0 : nadd, forall y1 : nadd, nadd_eq (nadd_mul y0 y1) (nadd_mul y1 y0)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y1 y2) -> nadd_le (nadd_mul y0 y1) (nadd_mul y0 y2)) -> False.
Definition term86 (x0 : nadd) (x1 : nadd) := and (nadd_le x0 x1).
Definition term185 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (nadd_eq x2 x0) /\ ((nadd_eq x3 x1) /\ (nadd_le x2 x3)).
Definition term117 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (~ (nadd_le x0 x2)) \/ (nadd_le (nadd_mul x1 x0) (nadd_mul x1 x2)).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term110 (x0 : nadd) (x1 : nadd) (x2 : nadd) := forall y0 : nadd, ((~ (nadd_eq x0 x2)) \/ (~ (nadd_eq x1 y0))) \/ (((nadd_le x0 x1) \/ (~ (nadd_le x2 y0))) /\ ((~ (nadd_le x0 x1)) \/ (nadd_le x2 y0))).
Definition term180 (x0 : nadd) (x1 : nadd) := and (~ (~ (nadd_eq x0 x1))).
Definition term155 (x0 : nadd) (x1 : nadd) (x2 : nadd) := @eq Prop ((nadd_le (nadd_mul x0 x1) (nadd_mul x0 x2)) \/ (~ (nadd_le x1 x2))).
Definition term184 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (nadd_eq x2 x0) /\ (nadd_le x1 x2).
Definition term98 := exists y0 : nadd, exists y1 : nadd, (nadd_le y0 y1) /\ (exists y2 : nadd, ~ (nadd_le (nadd_mul y0 y2) (nadd_mul y1 y2))).
Definition term76 := exists y0 : nadd, exists y1 : nadd, exists y2 : nadd, (nadd_le y0 y1) /\ (~ (nadd_le (nadd_mul y0 y2) (nadd_mul y1 y2))).
Definition term70 (x0 : nadd) := exists y0 : nadd, exists y1 : nadd, (nadd_le x0 y0) /\ (~ (nadd_le (nadd_mul x0 y1) (nadd_mul y0 y1))).
Definition term48 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, (nadd_le x0 x1) -> nadd_le (nadd_mul x0 y0) (nadd_mul x1 y0).
Definition term28 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, (nadd_le x0 y0) -> nadd_le (nadd_mul x1 x0) (nadd_mul x1 y0).
Definition term125 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (((~ (nadd_eq x0 x2)) \/ (~ (nadd_eq x1 x3))) \/ ((nadd_le x0 x1) \/ (~ (nadd_le x2 x3)))) /\ (((~ (nadd_eq x0 x2)) \/ (~ (nadd_eq x1 x3))) \/ ((~ (nadd_le x0 x1)) \/ (nadd_le x2 x3))).
Definition term102 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (~ (nadd_eq x0 x1)) \/ (~ (nadd_eq x2 x3)).
Definition term73 (x0 : nadd) := ~ ((fun y0 : nadd => forall y1 : nadd, forall y2 : nadd, (nadd_le y0 y1) -> nadd_le (nadd_mul y0 y2) (nadd_mul y1 y2)) x0).
Definition term62 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (nadd_le x0 x1) /\ (~ (nadd_le (nadd_mul x0 y0) (nadd_mul x1 y0))).
Definition term94 (x0 : nadd) (x1 : nadd) := (nadd_le x0 x1) /\ (exists y0 : nadd, ~ (nadd_le (nadd_mul x0 y0) (nadd_mul x1 y0))).
Definition term120 (x0 : nadd) (x1 : nadd) := forall y0 : nadd, (~ (nadd_le x0 y0)) \/ (nadd_le (nadd_mul x1 x0) (nadd_mul x1 y0)).
Definition term167 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (nadd_le x0 x1) \/ ((~ (nadd_eq x3 x1)) \/ (~ (nadd_le x2 x3))).
Definition term56 (x0 : nadd -> Prop) := exists y0 : nadd, ~ (x0 y0).
Definition term179 (x0 : nadd) (x1 : nadd) := ~ (~ (nadd_eq x0 x1)).
Definition term130 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => forall y1 : nadd, (((~ (nadd_eq x0 x1)) \/ (~ (nadd_eq y0 y1))) \/ ((nadd_le x0 y0) \/ (~ (nadd_le x1 y1)))) /\ (((~ (nadd_eq x0 x1)) \/ (~ (nadd_eq y0 y1))) \/ ((~ (nadd_le x0 y0)) \/ (nadd_le x1 y1))).
Definition term121 (x0 : nadd) := fun y0 : nadd => forall y1 : nadd, (~ (nadd_le y0 y1)) \/ (nadd_le (nadd_mul x0 y0) (nadd_mul x0 y1)).
Definition term111 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => forall y1 : nadd, ((~ (nadd_eq x0 x1)) \/ (~ (nadd_eq y0 y1))) \/ (((nadd_le x0 y0) \/ (~ (nadd_le x1 y1))) /\ ((~ (nadd_le x0 y0)) \/ (nadd_le x1 y1))).
Definition term49 (x0 : nadd) := fun y0 : nadd => forall y1 : nadd, (nadd_le x0 y0) -> nadd_le (nadd_mul x0 y1) (nadd_mul y0 y1).
Definition term35 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => forall y1 : nadd, ((nadd_eq x0 x1) /\ (nadd_eq y0 y1)) -> (nadd_le x0 y0) = (nadd_le x1 y1).
Definition term29 (x0 : nadd) := fun y0 : nadd => forall y1 : nadd, (nadd_le y0 y1) -> nadd_le (nadd_mul x0 y0) (nadd_mul x0 y1).
Definition term107 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := ((~ (nadd_eq x0 x2)) \/ (~ (nadd_eq x1 x3))) \/ (((nadd_le x0 x1) \/ (~ (nadd_le x2 x3))) /\ ((~ (nadd_le x0 x1)) \/ (nadd_le x2 x3))).
Definition term163 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ~ (nadd_le (nadd_mul x1 x0) (nadd_mul x1 x2)).
Definition term174 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (~ (nadd_eq x2 x0)) \/ ((~ (nadd_eq x3 x1)) \/ (~ (nadd_le x2 x3))).
Definition term182 (x0 : nadd) (x1 : nadd) (x2 : nadd) := ~ ((~ (nadd_eq x2 x0)) \/ (~ (nadd_le x1 x2))).
Definition term137 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => nadd_eq (nadd_mul x0 y0) (nadd_mul y0 x0)) x1.
Definition term34 (x0 : nadd) (x1 : nadd) (x2 : nadd) := forall y0 : nadd, ((nadd_eq x0 x2) /\ (nadd_eq x1 y0)) -> (nadd_le x0 x1) = (nadd_le x2 y0).
Definition term54 (x0 : nadd) (x1 : nadd) (x2 : nadd) := nadd_le (nadd_mul x0 x2) (nadd_mul x1 x2).
Definition term20 := (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, forall y3 : nadd, ((nadd_eq y0 y1) /\ (nadd_eq y2 y3)) -> (nadd_le y0 y2) = (nadd_le y1 y3)) -> ~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y1 y2) -> nadd_le (nadd_mul y0 y1) (nadd_mul y0 y2)).
Definition term143 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, (~ (nadd_le y0 y1)) \/ (nadd_le (nadd_mul x0 y0) (nadd_mul x0 y1))) x1.
Definition term66 (x0 : nadd) (x1 : nadd) := (fun y0 : nadd => forall y1 : nadd, (nadd_le x0 y0) -> nadd_le (nadd_mul x0 y1) (nadd_mul y0 y1)) x1.
Definition term178 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (~ (~ (nadd_eq x2 x0))) /\ (~ ((~ (nadd_eq x3 x1)) \/ (~ (nadd_le x2 x3)))).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term47 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (nadd_le x0 x1) -> nadd_le (nadd_mul x0 y0) (nadd_mul x1 y0).
Definition term154 (x0 : nadd) (x1 : nadd) (x2 : nadd) := @eq Prop ((~ (nadd_le x0 x2)) \/ (nadd_le (nadd_mul x1 x0) (nadd_mul x1 x2))).
Definition term92 (x0 : nadd) (x1 : nadd) := exists y0 : nadd, (fun y1 : nadd => ~ (nadd_le (nadd_mul x0 y1) (nadd_mul x1 y1))) y0.
Definition term33 (x0 : nadd) (x1 : nadd) (x2 : nadd) := fun y0 : nadd => ((nadd_eq x0 x2) /\ (nadd_eq x1 y0)) -> (nadd_le x0 x1) = (nadd_le x2 y0).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term27 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (nadd_le x0 y0) -> nadd_le (nadd_mul x1 x0) (nadd_mul x1 y0).
Definition term152 (x0 : nadd) (x1 : nadd) := ~ (nadd_le x0 x1).
Definition term157 (x0 : nadd) (x1 : nadd) (x2 : nadd) := (~ (~ (nadd_le x0 x2))) -> nadd_le (nadd_mul x1 x0) (nadd_mul x1 x2).
Definition term75 := fun y0 : nadd => exists y1 : nadd, exists y2 : nadd, (nadd_le y0 y1) /\ (~ (nadd_le (nadd_mul y0 y2) (nadd_mul y1 y2))).
Definition term127 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (~ (nadd_le x0 x1)) \/ (nadd_le x2 x3).
Definition term96 (x0 : nadd) := exists y0 : nadd, (nadd_le x0 y0) /\ (exists y1 : nadd, ~ (nadd_le (nadd_mul x0 y1) (nadd_mul y0 y1))).
Definition term64 (x0 : nadd) := ~ (forall y0 : nadd, forall y1 : nadd, (nadd_le x0 y0) -> nadd_le (nadd_mul x0 y1) (nadd_mul y0 y1)).
Definition term16 := ~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y1 y2) -> nadd_le (nadd_mul y0 y1) (nadd_mul y0 y2)).
Definition term10 := ~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y0 y1) -> nadd_le (nadd_mul y0 y2) (nadd_mul y1 y2)).
Definition term104 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := or (~ ((nadd_eq x0 x1) /\ (nadd_eq x2 x3))).
Definition term91 (x0 : nadd) (x1 : nadd) := fun y0 : nadd => (fun y1 : nadd => ~ (nadd_le (nadd_mul x0 y1) (nadd_mul x1 y1))) y0.
Definition term141 (x0 : nadd) (x1 : nadd) (x2 : nadd) (x3 : nadd) := (fun y0 : nadd => (((~ (nadd_eq x0 x2)) \/ (~ (nadd_eq x1 y0))) \/ ((nadd_le x0 x1) \/ (~ (nadd_le x2 y0)))) /\ (((~ (nadd_eq x0 x2)) \/ (~ (nadd_eq x1 y0))) \/ ((~ (nadd_le x0 x1)) \/ (nadd_le x2 y0)))) x3.
Definition term148 (x0 : nadd) (x1 : nadd) := (~ (nadd_eq (nadd_mul x1 x0) (nadd_mul x0 x1))) -> nadd_eq (nadd_mul x1 x0) (nadd_mul x0 x1).
Definition term24 := imp (~ (forall y0 : nadd, forall y1 : nadd, forall y2 : nadd, (nadd_le y0 y1) -> nadd_le (nadd_mul y0 y2) (nadd_mul y1 y2))).
Definition term67 (x0 : nadd) (x1 : nadd) := ~ ((fun y0 : nadd => forall y1 : nadd, (nadd_le x0 y0) -> nadd_le (nadd_mul x0 y1) (nadd_mul y0 y1)) x1).
Definition term160 (x0 : nadd) (x1 : nadd) := imp (~ (~ (nadd_le x0 x1))).
