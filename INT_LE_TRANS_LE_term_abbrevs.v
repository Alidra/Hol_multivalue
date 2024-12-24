Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term178 (x0 : int) (x1 : int) := (exists y0 : int, (fun y1 : int => (int_le x1 x0) /\ ((int_le x0 y1) /\ (~ (int_le x1 y1)))) y0) \/ ((~ (int_le x1 x0)) /\ (forall y0 : int, (~ (int_le x0 y0)) \/ (int_le x1 y0))).
Definition term153 (x0 : int) := or (exists y0 : int, exists y1 : int, (int_le x0 y0) /\ ((int_le y0 y1) /\ (~ (int_le x0 y1)))).
Definition term142 := or (exists y0 : int, exists y1 : int, exists y2 : int, (int_le y0 y1) /\ ((int_le y1 y2) /\ (~ (int_le y0 y2)))).
Definition term117 := or (exists y0 : int, exists y1 : int, (int_le y0 y1) /\ (exists y2 : int, (int_le y1 y2) /\ (~ (int_le y0 y2)))).
Definition term93 (x0 : int) := exists y0 : int, (int_le x0 y0) /\ (exists y1 : int, (int_le y0 y1) /\ (~ (int_le x0 y1))).
Definition term128 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (int_le x0 y0) /\ (~ (int_le x1 y0))) x2.
Definition term219 (x0 : int) (x1 : int) (x2 : int) := (int_le x0 x2) \/ (~ (int_le x1 x2)).
Definition term211 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, ((~ (int_le x0 y0)) \/ (~ (int_le y0 y1))) \/ (int_le x0 y1)) x1.
Definition term163 (x0 : int) := exists y0 : int, (fun y1 : int => exists y2 : int, (int_le x0 y1) /\ ((int_le y1 y2) /\ (~ (int_le x0 y2)))) y0.
Definition term148 := exists y0 : int, (fun y1 : int => exists y2 : int, exists y3 : int, (int_le y1 y2) /\ ((int_le y2 y3) /\ (~ (int_le y1 y3)))) y0.
Definition term119 := exists y0 : int, (fun y1 : int => exists y2 : int, (~ (int_le y1 y2)) /\ (forall y3 : int, (~ (int_le y2 y3)) \/ (int_le y1 y3))) y0.
Definition term114 := exists y0 : int, (fun y1 : int => exists y2 : int, (int_le y1 y2) /\ (exists y3 : int, (int_le y2 y3) /\ (~ (int_le y1 y3)))) y0.
Definition term42 (x0 : int -> Prop) := exists y0 : int, ~ (x0 y0).
Definition term134 (x0 : int) (x1 : int) (x2 : int) := (int_le x1 x0) /\ ((int_le x0 x2) /\ (~ (int_le x1 x2))).
Definition term41 (x0 : int -> Prop) := ~ (all x0).
Definition term205 (x0 : int) (x1 : int) := forall y0 : int, ((~ (int_le x1 x0)) \/ (~ (int_le x0 y0))) \/ (int_le x1 y0).
Definition term237 := (~ False) -> False.
Definition term208 := fun y0 : int => forall y1 : int, forall y2 : int, ((~ (int_le y0 y1)) \/ (~ (int_le y1 y2))) \/ (int_le y0 y2).
Definition term28 := fun y0 : int => forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2.
Definition term239 (x0 : int) := ~ (int_le x0 x0).
Definition term199 (x0 : int) (x1 : int) (x2 : int) := or (~ ((int_le x0 x1) /\ (int_le x1 x2))).
Definition term231 (x0 : Prop) := ~ (~ x0).
Definition term40 (x0 : int) (x1 : int) (x2 : int) := (~ (int_le x0 x2)) \/ (int_le x1 x2).
Definition term105 := fun y0 : int => exists y1 : int, (~ (int_le y0 y1)) /\ (forall y2 : int, (~ (int_le y1 y2)) \/ (int_le y0 y2)).
Definition term104 := fun y0 : int => exists y1 : int, (int_le y0 y1) /\ (exists y2 : int, (int_le y1 y2) /\ (~ (int_le y0 y2))).
Definition term79 (x0 : int -> Prop) (x1 : int -> Prop) := (exists y0 : int, x0 y0) \/ (exists y0 : int, x1 y0).
Definition term37 := fun y0 : int => forall y1 : int, (int_le y0 y1) = (forall y2 : int, (int_le y1 y2) -> int_le y0 y2).
Definition term57 (x0 : int) (x1 : int) := (int_le x1 x0) /\ (exists y0 : int, (int_le x0 y0) /\ (~ (int_le x1 y0))).
Definition term241 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((int_le x0 x2) \/ (~ (int_le x1 x2))).
Definition term83 (x0 : int) := fun y0 : int => (~ (int_le x0 y0)) /\ (forall y1 : int, (~ (int_le y0 y1)) \/ (int_le x0 y1)).
Definition term242 (x0 : int) (x1 : int) (x2 : int) := (~ (~ (int_le x0 x2))) -> int_le x1 x2.
Definition term230 (x0 : int) (x1 : int) (x2 : int) := (~ (~ (int_le x0 x1))) /\ (~ (~ (int_le x1 x2))).
Definition term77 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term156 := fun y0 : int => ((fun y1 : int => exists y2 : int, exists y3 : int, (int_le y1 y2) /\ ((int_le y2 y3) /\ (~ (int_le y1 y3)))) y0) \/ ((fun y1 : int => exists y2 : int, (~ (int_le y1 y2)) /\ (forall y3 : int, (~ (int_le y2 y3)) \/ (int_le y1 y3))) y0).
Definition term110 := fun y0 : int => ((fun y1 : int => exists y2 : int, (int_le y1 y2) /\ (exists y3 : int, (int_le y2 y3) /\ (~ (int_le y1 y3)))) y0) \/ ((fun y1 : int => exists y2 : int, (~ (int_le y1 y2)) /\ (forall y3 : int, (~ (int_le y2 y3)) \/ (int_le y1 y3))) y0).
Definition term71 (x0 : int) := (fun y0 : int => forall y1 : int, (int_le y0 y1) = (forall y2 : int, (int_le y1 y2) -> int_le y0 y2)) x0.
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term123 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term7 (x0 : Prop) := (~ x0) -> False.
Definition term52 (x0 : int) (x1 : int) := and (~ (int_le x0 x1)).
Definition term187 (x0 : int) (x1 : int) (x2 : int) := or ((int_le x1 x0) /\ ((int_le x0 x2) /\ (~ (int_le x1 x2)))).
Definition term174 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term234 (x0 : int) (x1 : int) (x2 : int) := imp (~ ((~ (int_le x0 x1)) \/ (~ (int_le x1 x2)))).
Definition term210 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, ((~ (int_le y0 y1)) \/ (~ (int_le y1 y2))) \/ (int_le y0 y2)) x0.
Definition term189 (x0 : int) (x1 : int) (x2 : int) := ((int_le x2 x1) /\ ((int_le x1 x0) /\ (~ (int_le x2 x0)))) \/ ((~ (int_le x2 x1)) /\ (forall y0 : int, (~ (int_le x1 y0)) \/ (int_le x2 y0))).
Definition term67 (x0 : int) := fun y0 : int => ~ ((fun y1 : int => (int_le x0 y1) = (forall y2 : int, (int_le y1 y2) -> int_le x0 y2)) y0).
Definition term47 (x0 : int) (x1 : int) := fun y0 : int => ~ ((fun y1 : int => (int_le x0 y1) -> int_le x1 y1) y0).
Definition term190 (x0 : int) (x1 : int) := fun y0 : int => ((fun y1 : int => (int_le x1 x0) /\ ((int_le x0 y1) /\ (~ (int_le x1 y1)))) y0) \/ ((~ (int_le x1 x0)) /\ (forall y1 : int, (~ (int_le x0 y1)) \/ (int_le x1 y1))).
Definition term195 := fun y0 : int => exists y1 : int, exists y2 : int, ((int_le y0 y1) /\ ((int_le y1 y2) /\ (~ (int_le y0 y2)))) \/ ((~ (int_le y0 y1)) /\ (forall y3 : int, (~ (int_le y1 y3)) \/ (int_le y0 y3))).
Definition term140 := fun y0 : int => exists y1 : int, exists y2 : int, (int_le y0 y1) /\ ((int_le y1 y2) /\ (~ (int_le y0 y2))).
Definition term33 (x0 : int) (x1 : int) := forall y0 : int, (int_le x0 y0) -> int_le x1 y0.
Definition term225 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term54 (x0 : int) (x1 : int) := (~ (int_le x1 x0)) /\ (forall y0 : int, (~ (int_le x0 y0)) \/ (int_le x1 y0)).
Definition term53 (x0 : int) (x1 : int) := (~ (int_le x1 x0)) /\ (forall y0 : int, (int_le x0 y0) -> int_le x1 y0).
Definition term176 (x0 : int -> Prop) (x1 : Prop) := (exists y0 : int, x0 y0) \/ x1.
Definition term122 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term50 (x0 : int) (x1 : int) := fun y0 : int => (~ (int_le x0 y0)) \/ (int_le x1 y0).
Definition term218 (x0 : Prop) := (~ x0) -> x0.
Definition term23 (x0 : int) (x1 : int) (x2 : int) := ((int_le x1 x0) /\ (int_le x0 x2)) -> int_le x1 x2.
Definition term12 := ((~ (forall y0 : int, forall y1 : int, (int_le y0 y1) = (forall y2 : int, (int_le y1 y2) -> int_le y0 y2))) -> (forall y0 : int, int_le y0 y0) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> False) -> (~ (forall y0 : int, forall y1 : int, (int_le y0 y1) = (forall y2 : int, (int_le y1 y2) -> int_le y0 y2))) -> (forall y0 : int, int_le y0 y0) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> False.
Definition term216 (x0 : int) (x1 : int) := ~ (int_le x0 x1).
Definition term179 (x0 : int) (x1 : int) := exists y0 : int, ((fun y1 : int => (int_le x1 x0) /\ ((int_le x0 y1) /\ (~ (int_le x1 y1)))) y0) \/ ((~ (int_le x1 x0)) /\ (forall y1 : int, (~ (int_le x0 y1)) \/ (int_le x1 y1))).
Definition term24 (x0 : int) (x1 : int) := fun y0 : int => ((int_le x1 x0) /\ (int_le x0 y0)) -> int_le x1 y0.
Definition term228 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term72 (x0 : int) := ~ ((fun y0 : int => forall y1 : int, (int_le y0 y1) = (forall y2 : int, (int_le y1 y2) -> int_le y0 y2)) x0).
Definition term85 (x0 : int) (x1 : int) := or ((fun y0 : int => (int_le x0 y0) /\ (exists y1 : int, (int_le y0 y1) /\ (~ (int_le x0 y1)))) x1).
Definition term223 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((~ (int_le x1 x0)) \/ ((~ (int_le x0 x2)) \/ (int_le x1 x2))).
Definition term18 := imp (forall y0 : int, int_le y0 y0).
Definition term224 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((int_le x0 x2) \/ ((~ (int_le x0 x1)) \/ (~ (int_le x1 x2)))).
Definition term240 (x0 : int) (x1 : int) (x2 : int) := @eq Prop ((~ (int_le x0 x2)) \/ (int_le x1 x2)).
Definition term108 (x0 : int) := (fun y0 : int => exists y1 : int, (~ (int_le y0 y1)) /\ (forall y2 : int, (~ (int_le y1 y2)) \/ (int_le y0 y2))) x0.
Definition term106 (x0 : int) := (fun y0 : int => exists y1 : int, (int_le y0 y1) /\ (exists y2 : int, (int_le y1 y2) /\ (~ (int_le y0 y2)))) x0.
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term22 := (~ (forall y0 : int, forall y1 : int, (int_le y0 y1) = (forall y2 : int, (int_le y1 y2) -> int_le y0 y2))) -> (forall y0 : int, int_le y0 y0) -> ~ (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2).
Definition term220 (x0 : int) (x1 : int) := or (~ (int_le x0 x1)).
Definition term157 := fun y0 : int => (exists y1 : int, exists y2 : int, (int_le y0 y1) /\ ((int_le y1 y2) /\ (~ (int_le y0 y2)))) \/ (exists y1 : int, (~ (int_le y0 y1)) /\ (forall y2 : int, (~ (int_le y1 y2)) \/ (int_le y0 y2))).
Definition term100 := fun y0 : int => (exists y1 : int, (int_le y0 y1) /\ (exists y2 : int, (int_le y1 y2) /\ (~ (int_le y0 y2)))) \/ (exists y1 : int, (~ (int_le y0 y1)) /\ (forall y2 : int, (~ (int_le y1 y2)) \/ (int_le y0 y2))).
Definition term137 (x0 : int) (x1 : int) := exists y0 : int, (int_le x1 x0) /\ ((int_le x0 y0) /\ (~ (int_le x1 y0))).
Definition term158 := exists y0 : int, (exists y1 : int, exists y2 : int, (int_le y0 y1) /\ ((int_le y1 y2) /\ (~ (int_le y0 y2)))) \/ (exists y1 : int, (~ (int_le y0 y1)) /\ (forall y2 : int, (~ (int_le y1 y2)) \/ (int_le y0 y2))).
Definition term101 := exists y0 : int, (exists y1 : int, (int_le y0 y1) /\ (exists y2 : int, (int_le y1 y2) /\ (~ (int_le y0 y2)))) \/ (exists y1 : int, (~ (int_le y0 y1)) /\ (forall y2 : int, (~ (int_le y1 y2)) \/ (int_le y0 y2))).
Definition term133 (x0 : int) (x1 : int) (x2 : int) := (int_le x1 x0) /\ ((fun y0 : int => (int_le x0 y0) /\ (~ (int_le x1 y0))) x2).
Definition term98 (x0 : int) := exists y0 : int, (~ (int_le x0 y0)) /\ (forall y1 : int, (~ (int_le y0 y1)) \/ (int_le x0 y1)).
Definition term34 (x0 : int) (x1 : int) := @eq Prop (int_le x0 x1).
Definition term214 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (~ (int_le x0 y0)) \/ (int_le x1 y0)) x2.
Definition term15 := (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> False.
Definition term51 (x0 : int) (x1 : int) := forall y0 : int, (~ (int_le x0 y0)) \/ (int_le x1 y0).
Definition term161 (x0 : int) (x1 : int) := (fun y0 : int => exists y1 : int, (int_le x0 y0) /\ ((int_le y0 y1) /\ (~ (int_le x0 y1)))) x1.
Definition term143 := (exists y0 : int, exists y1 : int, exists y2 : int, (int_le y0 y1) /\ ((int_le y1 y2) /\ (~ (int_le y0 y2)))) \/ (exists y0 : int, exists y1 : int, (~ (int_le y0 y1)) /\ (forall y2 : int, (~ (int_le y1 y2)) \/ (int_le y0 y2))).
Definition term121 := (exists y0 : int, exists y1 : int, (int_le y0 y1) /\ (exists y2 : int, (int_le y1 y2) /\ (~ (int_le y0 y2)))) \/ (exists y0 : int, exists y1 : int, (~ (int_le y0 y1)) /\ (forall y2 : int, (~ (int_le y1 y2)) \/ (int_le y0 y2))).
Definition term159 (x0 : int) := (exists y0 : int, (fun y1 : int => exists y2 : int, (int_le x0 y1) /\ ((int_le y1 y2) /\ (~ (int_le x0 y2)))) y0) \/ (exists y0 : int, (fun y1 : int => (~ (int_le x0 y1)) /\ (forall y2 : int, (~ (int_le y1 y2)) \/ (int_le x0 y2))) y0).
Definition term144 := (exists y0 : int, (fun y1 : int => exists y2 : int, exists y3 : int, (int_le y1 y2) /\ ((int_le y2 y3) /\ (~ (int_le y1 y3)))) y0) \/ (exists y0 : int, (fun y1 : int => exists y2 : int, (~ (int_le y1 y2)) /\ (forall y3 : int, (~ (int_le y2 y3)) \/ (int_le y1 y3))) y0).
Definition term103 := (exists y0 : int, (fun y1 : int => exists y2 : int, (int_le y1 y2) /\ (exists y3 : int, (int_le y2 y3) /\ (~ (int_le y1 y3)))) y0) \/ (exists y0 : int, (fun y1 : int => exists y2 : int, (~ (int_le y1 y2)) /\ (forall y3 : int, (~ (int_le y2 y3)) \/ (int_le y1 y3))) y0).
Definition term81 (x0 : int) := (exists y0 : int, (fun y1 : int => (int_le x0 y1) /\ (exists y2 : int, (int_le y1 y2) /\ (~ (int_le x0 y2)))) y0) \/ (exists y0 : int, (fun y1 : int => (~ (int_le x0 y1)) /\ (forall y2 : int, (~ (int_le y1 y2)) \/ (int_le x0 y2))) y0).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term169 (x0 : int) (x1 : int) := ((fun y0 : int => exists y1 : int, (int_le x0 y0) /\ ((int_le y0 y1) /\ (~ (int_le x0 y1)))) x1) \/ ((fun y0 : int => (~ (int_le x0 y0)) /\ (forall y1 : int, (~ (int_le y0 y1)) \/ (int_le x0 y1))) x1).
Definition term129 (x0 : int) (x1 : int) := fun y0 : int => (fun y1 : int => (int_le x0 y1) /\ (~ (int_le x1 y1))) y0.
Definition term30 := forall y0 : int, int_le y0 y0.
Definition term112 := @eq Prop (exists y0 : int, (exists y1 : int, (int_le y0 y1) /\ (exists y2 : int, (int_le y1 y2) /\ (~ (int_le y0 y2)))) \/ (exists y1 : int, (~ (int_le y0 y1)) /\ (forall y2 : int, (~ (int_le y1 y2)) \/ (int_le y0 y2)))).
Definition term111 := @eq Prop (exists y0 : int, ((fun y1 : int => exists y2 : int, (int_le y1 y2) /\ (exists y3 : int, (int_le y2 y3) /\ (~ (int_le y1 y3)))) y0) \/ ((fun y1 : int => exists y2 : int, (~ (int_le y1 y2)) /\ (forall y3 : int, (~ (int_le y2 y3)) \/ (int_le y1 y3))) y0)).
Definition term90 (x0 : int) := @eq Prop (exists y0 : int, ((int_le x0 y0) /\ (exists y1 : int, (int_le y0 y1) /\ (~ (int_le x0 y1)))) \/ ((~ (int_le x0 y0)) /\ (forall y1 : int, (~ (int_le y0 y1)) \/ (int_le x0 y1)))).
Definition term89 (x0 : int) := @eq Prop (exists y0 : int, ((fun y1 : int => (int_le x0 y1) /\ (exists y2 : int, (int_le y1 y2) /\ (~ (int_le x0 y2)))) y0) \/ ((fun y1 : int => (~ (int_le x0 y1)) /\ (forall y2 : int, (~ (int_le y1 y2)) \/ (int_le x0 y2))) y0)).
Definition term227 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term198 (x0 : int) (x1 : int) (x2 : int) := (~ (int_le x0 x1)) \/ (~ (int_le x1 x2)).
Definition term99 (x0 : int) := (exists y0 : int, (int_le x0 y0) /\ (exists y1 : int, (int_le y0 y1) /\ (~ (int_le x0 y1)))) \/ (exists y0 : int, (~ (int_le x0 y0)) /\ (forall y1 : int, (~ (int_le y0 y1)) \/ (int_le x0 y1))).
Definition term38 (x0 : int) (x1 : int) (x2 : int) := ~ ((int_le x0 x2) -> int_le x1 x2).
Definition term29 := fun y0 : int => int_le y0 y0.
Definition term63 (x0 : int) := ~ (forall y0 : int, (int_le x0 y0) = (forall y1 : int, (int_le y0 y1) -> int_le x0 y1)).
Definition term43 (x0 : int) (x1 : int) := ~ (forall y0 : int, (int_le x0 y0) -> int_le x1 y0).
Definition term125 (x0 : Prop) (x1 : int -> Prop) := exists y0 : int, x0 /\ (x1 y0).
Definition term20 := (forall y0 : int, int_le y0 y0) -> ~ (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2).
Definition term222 (x0 : int) (x1 : int) (x2 : int) := (int_le x0 x2) \/ ((~ (int_le x0 x1)) \/ (~ (int_le x1 x2))).
Definition term13 := (((~ (forall y0 : int, forall y1 : int, (int_le y0 y1) = (forall y2 : int, (int_le y1 y2) -> int_le y0 y2))) -> (forall y0 : int, int_le y0 y0) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> False) -> (~ (forall y0 : int, forall y1 : int, (int_le y0 y1) = (forall y2 : int, (int_le y1 y2) -> int_le y0 y2))) -> (forall y0 : int, int_le y0 y0) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> False) -> (~ (forall y0 : int, forall y1 : int, (int_le y0 y1) = (forall y2 : int, (int_le y1 y2) -> int_le y0 y2))) -> (forall y0 : int, int_le y0 y0) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> False.
Definition term182 (x0 : int) (x1 : int) := exists y0 : int, (fun y1 : int => (int_le x1 x0) /\ ((int_le x0 y1) /\ (~ (int_le x1 y1)))) y0.
Definition term130 (x0 : int) (x1 : int) := exists y0 : int, (fun y1 : int => (int_le x0 y1) /\ (~ (int_le x1 y1))) y0.
Definition term97 (x0 : int) := exists y0 : int, (fun y1 : int => (~ (int_le x0 y1)) /\ (forall y2 : int, (~ (int_le y1 y2)) \/ (int_le x0 y2))) y0.
Definition term92 (x0 : int) := exists y0 : int, (fun y1 : int => (int_le x0 y1) /\ (exists y2 : int, (int_le y1 y2) /\ (~ (int_le x0 y2)))) y0.
Definition term58 (x0 : int) (x1 : int) := or ((int_le x1 x0) /\ (~ (forall y0 : int, (int_le x0 y0) -> int_le x1 y0))).
Definition term56 (x0 : int) (x1 : int) := (int_le x1 x0) /\ (~ (forall y0 : int, (int_le x0 y0) -> int_le x1 y0)).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term209 := forall y0 : int, forall y1 : int, forall y2 : int, ((~ (int_le y0 y1)) \/ (~ (int_le y1 y2))) \/ (int_le y0 y2).
Definition term207 (x0 : int) := forall y0 : int, forall y1 : int, ((~ (int_le x0 y0)) \/ (~ (int_le y0 y1))) \/ (int_le x0 y1).
Definition term27 (x0 : int) := forall y0 : int, forall y1 : int, ((int_le x0 y0) /\ (int_le y0 y1)) -> int_le x0 y1.
Definition term17 := forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2.
Definition term8 := forall y0 : int, forall y1 : int, (int_le y0 y1) = (forall y2 : int, (int_le y1 y2) -> int_le y0 y2).
Definition term19 := (forall y0 : int, int_le y0 y0) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> False.
Definition term175 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term126 (x0 : int) (x1 : int) := (int_le x1 x0) /\ (exists y0 : int, (fun y1 : int => (int_le x0 y1) /\ (~ (int_le x1 y1))) y0).
Definition term200 (x0 : int) (x1 : int) (x2 : int) := or ((~ (int_le x0 x1)) \/ (~ (int_le x1 x2))).
Definition term186 (x0 : int) (x1 : int) (x2 : int) := or ((fun y0 : int => (int_le x1 x0) /\ ((int_le x0 y0) /\ (~ (int_le x1 y0)))) x2).
Definition term9 := (~ (forall y0 : int, forall y1 : int, (int_le y0 y1) = (forall y2 : int, (int_le y1 y2) -> int_le y0 y2))) -> False.
Definition term202 (x0 : int) (x1 : int) (x2 : int) := ((~ (int_le x1 x0)) \/ (~ (int_le x0 x2))) \/ (int_le x1 x2).
Definition term236 (x0 : int) (x1 : int) := (int_le x0 x1) -> False.
Definition term206 (x0 : int) := fun y0 : int => forall y1 : int, ((~ (int_le x0 y0)) \/ (~ (int_le y0 y1))) \/ (int_le x0 y1).
Definition term26 (x0 : int) := fun y0 : int => forall y1 : int, ((int_le x0 y0) /\ (int_le y0 y1)) -> int_le x0 y1.
Definition term171 (x0 : int) := fun y0 : int => ((fun y1 : int => exists y2 : int, (int_le x0 y1) /\ ((int_le y1 y2) /\ (~ (int_le x0 y2)))) y0) \/ ((fun y1 : int => (~ (int_le x0 y1)) /\ (forall y2 : int, (~ (int_le y1 y2)) \/ (int_le x0 y2))) y0).
Definition term88 (x0 : int) := fun y0 : int => ((fun y1 : int => (int_le x0 y1) /\ (exists y2 : int, (int_le y1 y2) /\ (~ (int_le x0 y2)))) y0) \/ ((fun y1 : int => (~ (int_le x0 y1)) /\ (forall y2 : int, (~ (int_le y1 y2)) \/ (int_le x0 y2))) y0).
Definition term62 (x0 : int) (x1 : int) := ~ ((int_le x1 x0) = (forall y0 : int, (int_le x0 y0) -> int_le x1 y0)).
Definition term191 (x0 : int) (x1 : int) := fun y0 : int => ((int_le x1 x0) /\ ((int_le x0 y0) /\ (~ (int_le x1 y0)))) \/ ((~ (int_le x1 x0)) /\ (forall y1 : int, (~ (int_le x0 y1)) \/ (int_le x1 y1))).
Definition term136 (x0 : int) (x1 : int) := fun y0 : int => (int_le x1 x0) /\ ((int_le x0 y0) /\ (~ (int_le x1 y0))).
Definition term14 := (((~ (forall y0 : int, forall y1 : int, (int_le y0 y1) = (forall y2 : int, (int_le y1 y2) -> int_le y0 y2))) -> (forall y0 : int, int_le y0 y0) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> False) -> (~ (forall y0 : int, forall y1 : int, (int_le y0 y1) = (forall y2 : int, (int_le y1 y2) -> int_le y0 y2))) -> (forall y0 : int, int_le y0 y0) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> False) -> ((~ (forall y0 : int, forall y1 : int, (int_le y0 y1) = (forall y2 : int, (int_le y1 y2) -> int_le y0 y2))) -> (forall y0 : int, int_le y0 y0) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> False) -> (~ (forall y0 : int, forall y1 : int, (int_le y0 y1) = (forall y2 : int, (int_le y1 y2) -> int_le y0 y2))) -> (forall y0 : int, int_le y0 y0) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> False.
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term46 (x0 : int) (x1 : int) (x2 : int) := ~ ((fun y0 : int => (int_le x0 y0) -> int_le x1 y0) x2).
Definition term60 (x0 : int) (x1 : int) := ((int_le x1 x0) /\ (~ (forall y0 : int, (int_le x0 y0) -> int_le x1 y0))) \/ ((~ (int_le x1 x0)) /\ (forall y0 : int, (int_le x0 y0) -> int_le x1 y0)).
Definition term233 (x0 : int) (x1 : int) := and (~ (~ (int_le x0 x1))).
Definition term192 (x0 : int) (x1 : int) := exists y0 : int, ((int_le x1 x0) /\ ((int_le x0 y0) /\ (~ (int_le x1 y0)))) \/ ((~ (int_le x1 x0)) /\ (forall y1 : int, (~ (int_le x0 y1)) \/ (int_le x1 y1))).
Definition term69 (x0 : int) := exists y0 : int, ((int_le x0 y0) /\ (exists y1 : int, (int_le y0 y1) /\ (~ (int_le x0 y1)))) \/ ((~ (int_le x0 y0)) /\ (forall y1 : int, (~ (int_le y0 y1)) \/ (int_le x0 y1))).
Definition term16 := ~ (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2).
Definition term10 := ~ (forall y0 : int, forall y1 : int, (int_le y0 y1) = (forall y2 : int, (int_le y1 y2) -> int_le y0 y2)).
Definition term245 (x0 : int) (x1 : int) := (int_le x1 x1) -> int_le x0 x1.
Definition term167 (x0 : int) (x1 : int) := or ((fun y0 : int => exists y1 : int, (int_le x0 y0) /\ ((int_le y0 y1) /\ (~ (int_le x0 y1)))) x1).
Definition term170 (x0 : int) (x1 : int) := (exists y0 : int, (int_le x1 x0) /\ ((int_le x0 y0) /\ (~ (int_le x1 y0)))) \/ ((~ (int_le x1 x0)) /\ (forall y0 : int, (~ (int_le x0 y0)) \/ (int_le x1 y0))).
Definition term66 (x0 : int) (x1 : int) := ~ ((fun y0 : int => (int_le x0 y0) = (forall y1 : int, (int_le y0 y1) -> int_le x0 y1)) x1).
Definition term154 (x0 : int) := ((fun y0 : int => exists y1 : int, exists y2 : int, (int_le y0 y1) /\ ((int_le y1 y2) /\ (~ (int_le y0 y2)))) x0) \/ ((fun y0 : int => exists y1 : int, (~ (int_le y0 y1)) /\ (forall y2 : int, (~ (int_le y1 y2)) \/ (int_le y0 y2))) x0).
Definition term109 (x0 : int) := ((fun y0 : int => exists y1 : int, (int_le y0 y1) /\ (exists y2 : int, (int_le y1 y2) /\ (~ (int_le y0 y2)))) x0) \/ ((fun y0 : int => exists y1 : int, (~ (int_le y0 y1)) /\ (forall y2 : int, (~ (int_le y1 y2)) \/ (int_le y0 y2))) x0).
Definition term96 (x0 : int) := fun y0 : int => (fun y1 : int => (~ (int_le x0 y1)) /\ (forall y2 : int, (~ (int_le y1 y2)) \/ (int_le x0 y2))) y0.
Definition term91 (x0 : int) := fun y0 : int => (fun y1 : int => (int_le x0 y1) /\ (exists y2 : int, (int_le y1 y2) /\ (~ (int_le x0 y2)))) y0.
Definition term135 (x0 : int) (x1 : int) := fun y0 : int => (int_le x1 x0) /\ ((fun y1 : int => (int_le x0 y1) /\ (~ (int_le x1 y1))) y0).
Definition term84 (x0 : int) (x1 : int) := (fun y0 : int => (int_le x0 y0) /\ (exists y1 : int, (int_le y0 y1) /\ (~ (int_le x0 y1)))) x1.
Definition term127 (x0 : int) (x1 : int) := exists y0 : int, (int_le x1 x0) /\ ((fun y1 : int => (int_le x0 y1) /\ (~ (int_le x1 y1))) y0).
Definition term235 (x0 : int) (x1 : int) (x2 : int) := imp ((int_le x0 x1) /\ (int_le x1 x2)).
Definition term204 (x0 : int) (x1 : int) := fun y0 : int => ((~ (int_le x1 x0)) \/ (~ (int_le x0 y0))) \/ (int_le x1 y0).
Definition term25 (x0 : int) (x1 : int) := forall y0 : int, ((int_le x1 x0) /\ (int_le x0 y0)) -> int_le x1 y0.
Definition term188 (x0 : int) (x1 : int) (x2 : int) := ((fun y0 : int => (int_le x2 x1) /\ ((int_le x1 y0) /\ (~ (int_le x2 y0)))) x0) \/ ((~ (int_le x2 x1)) /\ (forall y0 : int, (~ (int_le x1 y0)) \/ (int_le x2 y0))).
Definition term146 (x0 : int) := (fun y0 : int => exists y1 : int, exists y2 : int, (int_le y0 y1) /\ ((int_le y1 y2) /\ (~ (int_le y0 y2)))) x0.
Definition term55 (x0 : int) (x1 : int) := and (int_le x0 x1).
Definition term173 (x0 : int) := exists y0 : int, (exists y1 : int, (int_le x0 y0) /\ ((int_le y0 y1) /\ (~ (int_le x0 y1)))) \/ ((~ (int_le x0 y0)) /\ (forall y1 : int, (~ (int_le y0 y1)) \/ (int_le x0 y1))).
Definition term152 (x0 : int) := or ((fun y0 : int => exists y1 : int, exists y2 : int, (int_le y0 y1) /\ ((int_le y1 y2) /\ (~ (int_le y0 y2)))) x0).
Definition term107 (x0 : int) := or ((fun y0 : int => exists y1 : int, (int_le y0 y1) /\ (exists y2 : int, (int_le y1 y2) /\ (~ (int_le y0 y2)))) x0).
Definition term45 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (int_le x0 y0) -> int_le x1 y0) x2.
Definition term238 (x0 : int) := (~ (int_le x0 x0)) -> int_le x0 x0.
Definition term78 (x0 : int -> Prop) (x1 : int -> Prop) := exists y0 : int, (x0 y0) \/ (x1 y0).
Definition term87 (x0 : int) (x1 : int) := ((fun y0 : int => (int_le x0 y0) /\ (exists y1 : int, (int_le y0 y1) /\ (~ (int_le x0 y1)))) x1) \/ ((fun y0 : int => (~ (int_le x0 y0)) /\ (forall y1 : int, (~ (int_le y0 y1)) \/ (int_le x0 y1))) x1).
Definition term36 (x0 : int) := forall y0 : int, (int_le x0 y0) = (forall y1 : int, (int_le y0 y1) -> int_le x0 y1).
Definition term181 (x0 : int) (x1 : int) := fun y0 : int => (fun y1 : int => (int_le x1 x0) /\ ((int_le x0 y1) /\ (~ (int_le x1 y1)))) y0.
Definition term244 (x0 : int) (x1 : int) := imp (int_le x0 x1).
Definition term185 (x0 : int) (x1 : int) := @eq Prop ((exists y0 : int, (int_le x1 x0) /\ ((int_le x0 y0) /\ (~ (int_le x1 y0)))) \/ ((~ (int_le x1 x0)) /\ (forall y0 : int, (~ (int_le x0 y0)) \/ (int_le x1 y0)))).
Definition term184 (x0 : int) (x1 : int) := @eq Prop ((exists y0 : int, (fun y1 : int => (int_le x1 x0) /\ ((int_le x0 y1) /\ (~ (int_le x1 y1)))) y0) \/ ((~ (int_le x1 x0)) /\ (forall y0 : int, (~ (int_le x0 y0)) \/ (int_le x1 y0)))).
Definition term132 (x0 : int) (x1 : int) := @eq Prop ((int_le x1 x0) /\ (exists y0 : int, (int_le x0 y0) /\ (~ (int_le x1 y0)))).
Definition term131 (x0 : int) (x1 : int) := @eq Prop ((int_le x1 x0) /\ (exists y0 : int, (fun y1 : int => (int_le x0 y1) /\ (~ (int_le x1 y1))) y0)).
Definition term229 (x0 : int) (x1 : int) (x2 : int) := ~ ((~ (int_le x0 x1)) \/ (~ (int_le x1 x2))).
Definition term201 (x0 : int) (x1 : int) (x2 : int) := (~ ((int_le x1 x0) /\ (int_le x0 x2))) \/ (int_le x1 x2).
Definition term61 (x0 : int) (x1 : int) := ((int_le x1 x0) /\ (exists y0 : int, (int_le x0 y0) /\ (~ (int_le x1 y0)))) \/ ((~ (int_le x1 x0)) /\ (forall y0 : int, (~ (int_le x0 y0)) \/ (int_le x1 y0))).
Definition term168 (x0 : int) (x1 : int) := or (exists y0 : int, (int_le x1 x0) /\ ((int_le x0 y0) /\ (~ (int_le x1 y0)))).
Definition term95 (x0 : int) := or (exists y0 : int, (int_le x0 y0) /\ (exists y1 : int, (int_le y0 y1) /\ (~ (int_le x0 y1)))).
Definition term32 (x0 : int) (x1 : int) := fun y0 : int => (int_le x0 y0) -> int_le x1 y0.
Definition term68 (x0 : int) := fun y0 : int => ((int_le x0 y0) /\ (exists y1 : int, (int_le y0 y1) /\ (~ (int_le x0 y1)))) \/ ((~ (int_le x0 y0)) /\ (forall y1 : int, (~ (int_le y0 y1)) \/ (int_le x0 y1))).
Definition term160 (x0 : int) := exists y0 : int, ((fun y1 : int => exists y2 : int, (int_le x0 y1) /\ ((int_le y1 y2) /\ (~ (int_le x0 y2)))) y0) \/ ((fun y1 : int => (~ (int_le x0 y1)) /\ (forall y2 : int, (~ (int_le y1 y2)) \/ (int_le x0 y2))) y0).
Definition term145 := exists y0 : int, ((fun y1 : int => exists y2 : int, exists y3 : int, (int_le y1 y2) /\ ((int_le y2 y3) /\ (~ (int_le y1 y3)))) y0) \/ ((fun y1 : int => exists y2 : int, (~ (int_le y1 y2)) /\ (forall y3 : int, (~ (int_le y2 y3)) \/ (int_le y1 y3))) y0).
Definition term102 := exists y0 : int, ((fun y1 : int => exists y2 : int, (int_le y1 y2) /\ (exists y3 : int, (int_le y2 y3) /\ (~ (int_le y1 y3)))) y0) \/ ((fun y1 : int => exists y2 : int, (~ (int_le y1 y2)) /\ (forall y3 : int, (~ (int_le y2 y3)) \/ (int_le y1 y3))) y0).
Definition term80 (x0 : int) := exists y0 : int, ((fun y1 : int => (int_le x0 y1) /\ (exists y2 : int, (int_le y1 y2) /\ (~ (int_le x0 y2)))) y0) \/ ((fun y1 : int => (~ (int_le x0 y1)) /\ (forall y2 : int, (~ (int_le y1 y2)) \/ (int_le x0 y2))) y0).
Definition term39 (x0 : int) (x1 : int) (x2 : int) := (int_le x0 x2) /\ (~ (int_le x1 x2)).
Definition term86 (x0 : int) (x1 : int) := (fun y0 : int => (~ (int_le x0 y0)) /\ (forall y1 : int, (~ (int_le y0 y1)) \/ (int_le x0 y1))) x1.
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term197 (x0 : int) (x1 : int) (x2 : int) := ~ ((int_le x0 x1) /\ (int_le x1 x2)).
Definition term203 (x0 : int) (x1 : int) (x2 : int) := (int_le x0 x1) /\ (int_le x1 x2).
Definition term59 (x0 : int) (x1 : int) := or ((int_le x1 x0) /\ (exists y0 : int, (int_le x0 y0) /\ (~ (int_le x1 y0)))).
Definition term183 (x0 : int) (x1 : int) := or (exists y0 : int, (fun y1 : int => (int_le x1 x0) /\ ((int_le x0 y1) /\ (~ (int_le x1 y1)))) y0).
Definition term164 (x0 : int) := or (exists y0 : int, (fun y1 : int => exists y2 : int, (int_le x0 y1) /\ ((int_le y1 y2) /\ (~ (int_le x0 y2)))) y0).
Definition term149 := or (exists y0 : int, (fun y1 : int => exists y2 : int, exists y3 : int, (int_le y1 y2) /\ ((int_le y2 y3) /\ (~ (int_le y1 y3)))) y0).
Definition term116 := or (exists y0 : int, (fun y1 : int => exists y2 : int, (int_le y1 y2) /\ (exists y3 : int, (int_le y2 y3) /\ (~ (int_le y1 y3)))) y0).
Definition term94 (x0 : int) := or (exists y0 : int, (fun y1 : int => (int_le x0 y1) /\ (exists y2 : int, (int_le y1 y2) /\ (~ (int_le x0 y2)))) y0).
Definition term70 := exists y0 : int, ~ ((fun y1 : int => forall y2 : int, (int_le y1 y2) = (forall y3 : int, (int_le y2 y3) -> int_le y1 y3)) y0).
Definition term64 (x0 : int) := exists y0 : int, ~ ((fun y1 : int => (int_le x0 y1) = (forall y2 : int, (int_le y1 y2) -> int_le x0 y2)) y0).
Definition term44 (x0 : int) (x1 : int) := exists y0 : int, ~ ((fun y1 : int => (int_le x0 y1) -> int_le x1 y1) y0).
Definition term48 (x0 : int) (x1 : int) := fun y0 : int => (int_le x0 y0) /\ (~ (int_le x1 y0)).
Definition term124 (x0 : Prop) (x1 : int -> Prop) := x0 /\ (exists y0 : int, x1 y0).
Definition term196 := exists y0 : int, exists y1 : int, exists y2 : int, ((int_le y0 y1) /\ ((int_le y1 y2) /\ (~ (int_le y0 y2)))) \/ ((~ (int_le y0 y1)) /\ (forall y3 : int, (~ (int_le y1 y3)) \/ (int_le y0 y3))).
Definition term194 (x0 : int) := exists y0 : int, exists y1 : int, ((int_le x0 y0) /\ ((int_le y0 y1) /\ (~ (int_le x0 y1)))) \/ ((~ (int_le x0 y0)) /\ (forall y2 : int, (~ (int_le y0 y2)) \/ (int_le x0 y2))).
Definition term141 := exists y0 : int, exists y1 : int, exists y2 : int, (int_le y0 y1) /\ ((int_le y1 y2) /\ (~ (int_le y0 y2))).
Definition term139 (x0 : int) := exists y0 : int, exists y1 : int, (int_le x0 y0) /\ ((int_le y0 y1) /\ (~ (int_le x0 y1))).
Definition term120 := exists y0 : int, exists y1 : int, (~ (int_le y0 y1)) /\ (forall y2 : int, (~ (int_le y1 y2)) \/ (int_le y0 y2)).
Definition term115 := exists y0 : int, exists y1 : int, (int_le y0 y1) /\ (exists y2 : int, (int_le y1 y2) /\ (~ (int_le y0 y2))).
Definition term75 := exists y0 : int, exists y1 : int, ((int_le y0 y1) /\ (exists y2 : int, (int_le y1 y2) /\ (~ (int_le y0 y2)))) \/ ((~ (int_le y0 y1)) /\ (forall y2 : int, (~ (int_le y1 y2)) \/ (int_le y0 y2))).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term193 (x0 : int) := fun y0 : int => exists y1 : int, ((int_le x0 y0) /\ ((int_le y0 y1) /\ (~ (int_le x0 y1)))) \/ ((~ (int_le x0 y0)) /\ (forall y2 : int, (~ (int_le y0 y2)) \/ (int_le x0 y2))).
Definition term138 (x0 : int) := fun y0 : int => exists y1 : int, (int_le x0 y0) /\ ((int_le y0 y1) /\ (~ (int_le x0 y1))).
Definition term74 := fun y0 : int => exists y1 : int, ((int_le y0 y1) /\ (exists y2 : int, (int_le y1 y2) /\ (~ (int_le y0 y2)))) \/ ((~ (int_le y0 y1)) /\ (forall y2 : int, (~ (int_le y1 y2)) \/ (int_le y0 y2))).
Definition term172 (x0 : int) := fun y0 : int => (exists y1 : int, (int_le x0 y0) /\ ((int_le y0 y1) /\ (~ (int_le x0 y1)))) \/ ((~ (int_le x0 y0)) /\ (forall y1 : int, (~ (int_le y0 y1)) \/ (int_le x0 y1))).
Definition term221 (x0 : int) (x1 : int) (x2 : int) := (~ (int_le x0 x1)) \/ ((int_le x0 x2) \/ (~ (int_le x1 x2))).
Definition term213 (x0 : int) := (fun y0 : int => int_le y0 y0) x0.
Definition term180 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (int_le x1 x0) /\ ((int_le x0 y0) /\ (~ (int_le x1 y0)))) x2.
Definition term31 (x0 : int) (x1 : int) (x2 : int) := (int_le x0 x2) -> int_le x1 x2.
Definition term35 (x0 : int) := fun y0 : int => (int_le x0 y0) = (forall y1 : int, (int_le y0 y1) -> int_le x0 y1).
Definition term162 (x0 : int) := fun y0 : int => (fun y1 : int => exists y2 : int, (int_le x0 y1) /\ ((int_le y1 y2) /\ (~ (int_le x0 y2)))) y0.
Definition term147 := fun y0 : int => (fun y1 : int => exists y2 : int, exists y3 : int, (int_le y1 y2) /\ ((int_le y2 y3) /\ (~ (int_le y1 y3)))) y0.
Definition term118 := fun y0 : int => (fun y1 : int => exists y2 : int, (~ (int_le y1 y2)) /\ (forall y3 : int, (~ (int_le y2 y3)) \/ (int_le y1 y3))) y0.
Definition term113 := fun y0 : int => (fun y1 : int => exists y2 : int, (int_le y1 y2) /\ (exists y3 : int, (int_le y2 y3) /\ (~ (int_le y1 y3)))) y0.
Definition term82 (x0 : int) := fun y0 : int => (int_le x0 y0) /\ (exists y1 : int, (int_le y0 y1) /\ (~ (int_le x0 y1))).
Definition term65 (x0 : int) (x1 : int) := (fun y0 : int => (int_le x0 y0) = (forall y1 : int, (int_le y0 y1) -> int_le x0 y1)) x1.
Definition term76 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term11 := (~ (forall y0 : int, forall y1 : int, (int_le y0 y1) = (forall y2 : int, (int_le y1 y2) -> int_le y0 y2))) -> (forall y0 : int, int_le y0 y0) -> (forall y0 : int, forall y1 : int, forall y2 : int, ((int_le y0 y1) /\ (int_le y1 y2)) -> int_le y0 y2) -> False.
Definition term215 (x0 : int) (x1 : int) (x2 : int) := (~ (int_le x1 x0)) \/ ((~ (int_le x0 x2)) \/ (int_le x1 x2)).
Definition term49 (x0 : int) (x1 : int) := exists y0 : int, (int_le x0 y0) /\ (~ (int_le x1 y0)).
Definition term212 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => ((~ (int_le x1 x0)) \/ (~ (int_le x0 y0))) \/ (int_le x1 y0)) x2.
Definition term232 (x0 : int) (x1 : int) := ~ (~ (int_le x0 x1)).
Definition term217 (x0 : int) (x1 : int) := (~ (int_le x0 x1)) -> int_le x0 x1.
Definition term226 (x0 : int) (x1 : int) (x2 : int) := (~ ((~ (int_le x1 x0)) \/ (~ (int_le x0 x2)))) -> int_le x1 x2.
Definition term21 := imp (~ (forall y0 : int, forall y1 : int, (int_le y0 y1) = (forall y2 : int, (int_le y1 y2) -> int_le y0 y2))).
Definition term155 (x0 : int) := (exists y0 : int, exists y1 : int, (int_le x0 y0) /\ ((int_le y0 y1) /\ (~ (int_le x0 y1)))) \/ (exists y0 : int, (~ (int_le x0 y0)) /\ (forall y1 : int, (~ (int_le y0 y1)) \/ (int_le x0 y1))).
Definition term73 := fun y0 : int => ~ ((fun y1 : int => forall y2 : int, (int_le y1 y2) = (forall y3 : int, (int_le y2 y3) -> int_le y1 y3)) y0).
Definition term177 (x0 : int -> Prop) (x1 : Prop) := exists y0 : int, (x0 y0) \/ x1.
Definition term243 (x0 : int) (x1 : int) := imp (~ (~ (int_le x0 x1))).
Definition term166 (x0 : int) := @eq Prop ((exists y0 : int, exists y1 : int, (int_le x0 y0) /\ ((int_le y0 y1) /\ (~ (int_le x0 y1)))) \/ (exists y0 : int, (~ (int_le x0 y0)) /\ (forall y1 : int, (~ (int_le y0 y1)) \/ (int_le x0 y1)))).
Definition term165 (x0 : int) := @eq Prop ((exists y0 : int, (fun y1 : int => exists y2 : int, (int_le x0 y1) /\ ((int_le y1 y2) /\ (~ (int_le x0 y2)))) y0) \/ (exists y0 : int, (fun y1 : int => (~ (int_le x0 y1)) /\ (forall y2 : int, (~ (int_le y1 y2)) \/ (int_le x0 y2))) y0)).
Definition term151 := @eq Prop ((exists y0 : int, exists y1 : int, exists y2 : int, (int_le y0 y1) /\ ((int_le y1 y2) /\ (~ (int_le y0 y2)))) \/ (exists y0 : int, exists y1 : int, (~ (int_le y0 y1)) /\ (forall y2 : int, (~ (int_le y1 y2)) \/ (int_le y0 y2)))).
Definition term150 := @eq Prop ((exists y0 : int, (fun y1 : int => exists y2 : int, exists y3 : int, (int_le y1 y2) /\ ((int_le y2 y3) /\ (~ (int_le y1 y3)))) y0) \/ (exists y0 : int, (fun y1 : int => exists y2 : int, (~ (int_le y1 y2)) /\ (forall y3 : int, (~ (int_le y2 y3)) \/ (int_le y1 y3))) y0)).
