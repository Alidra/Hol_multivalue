Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term112 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := fun y0 : a1 => (forall y1 : prod a1 a0, ~ (x0 y1)) /\ ((fun y1 : a1 => exists y2 : a0, x0 (@pair a1 a0 y1 y2)) y0).
Definition term26 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := ~ (exists y0 : prod a1 a0, x0 y0).
Definition term121 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) (x2 : a0) := (forall y0 : prod a1 a0, ~ (x0 y0)) /\ ((fun y0 : a0 => x0 (@pair a1 a0 x1 y0)) x2).
Definition term256 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) (x2 : prod a1 a0) := ~ ((~ (x2 = x0)) \/ (~ (x1 x2))).
Definition term182 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) := fun y0 : a1 => ((x1 x0) /\ (forall y1 : a1, forall y2 : a0, ~ (x1 (@pair a1 a0 y1 y2)))) \/ (exists y1 : a0, (forall y2 : prod a1 a0, ~ (x1 y2)) /\ (x1 (@pair a1 a0 y0 y1))).
Definition term104 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (forall y0 : prod a1 a0, ~ (x0 y0)) /\ (exists y0 : a1, (fun y1 : a1 => exists y2 : a0, x0 (@pair a1 a0 y1 y2)) y0).
Definition term191 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) (x2 : a1) (x3 : a0) := ((x1 x0) /\ (forall y0 : a1, forall y1 : a0, ~ (x1 (@pair a1 a0 y0 y1)))) \/ ((fun y0 : a0 => (forall y1 : prod a1 a0, ~ (x1 y1)) /\ (x1 (@pair a1 a0 x2 y0))) x3).
Definition term62 (a0 : Type') (a1 : Type') (x0 : type330 a0 a1) := ~ (all x0).
Definition term270 := (~ False) -> False.
Definition term5 (a0 : Type') (a1 : Type') := (~ (forall y0 : type1223 a0 a1, (exists y1 : prod a1 a0, y0 y1) = (exists y1 : a1, exists y2 : a0, y0 (@pair a1 a0 y1 y2)))) -> (forall y0 : prod a1 a0, (@pair a1 a0 (@fst a1 a0 y0) (@snd a1 a0 y0)) = y0) -> False.
Definition term91 (a0 : Type') (a1 : Type') := exists y0 : type1223 a0 a1, (fun y1 : type1223 a0 a1 => (forall y2 : prod a1 a0, ~ (y1 y2)) /\ (exists y2 : a1, exists y3 : a0, y1 (@pair a1 a0 y2 y3))) y0.
Definition term86 (a0 : Type') (a1 : Type') := exists y0 : type1223 a0 a1, (fun y1 : type1223 a0 a1 => (exists y2 : prod a1 a0, y1 y2) /\ (forall y2 : a1, forall y3 : a0, ~ (y1 (@pair a1 a0 y2 y3)))) y0.
Definition term61 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := ~ ((exists y0 : prod a1 a0, x0 y0) = (exists y0 : a1, exists y1 : a0, x0 (@pair a1 a0 y0 y1))).
Definition term196 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) := fun y0 : a1 => exists y1 : a0, ((x1 x0) /\ (forall y2 : a1, forall y3 : a0, ~ (x1 (@pair a1 a0 y2 y3)))) \/ ((forall y2 : prod a1 a0, ~ (x1 y2)) /\ (x1 (@pair a1 a0 y0 y1))).
Definition term41 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) := fun y0 : a0 => ~ (x0 (@pair a1 a0 x1 y0)).
Definition term25 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : prod a1 a0, ~ (x0 y0).
Definition term100 (a0 : Type') (a1 : Type') := exists y0 : type1223 a0 a1, exists y1 : prod a1 a0, (y0 y1) /\ (forall y2 : a1, forall y3 : a0, ~ (y0 (@pair a1 a0 y2 y3))).
Definition term215 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) := ~ ((@pair a1 a0 (@fst a1 a0 x0) (@snd a1 a0 x0)) = x0).
Definition term206 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : prod a1 a0) := (fun y0 : prod a1 a0 => ~ (x0 y0)) x1.
Definition term235 (x0 : Prop) := ~ (~ x0).
Definition term52 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (~ (exists y0 : prod a1 a0, x0 y0)) /\ (exists y0 : a1, exists y1 : a0, x0 (@pair a1 a0 y0 y1)).
Definition term40 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) := fun y0 : a0 => ~ ((fun y1 : a0 => x0 (@pair a1 a0 x1 y1)) y0).
Definition term64 (a0 : Type') (a1 : Type') := exists y0 : type1223 a0 a1, ~ ((fun y1 : type1223 a0 a1 => (exists y2 : prod a1 a0, y1 y2) = (exists y2 : a1, exists y3 : a0, y1 (@pair a1 a0 y2 y3))) y0).
Definition term257 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) (x2 : prod a1 a0) := (~ (~ (x2 = x0))) /\ (~ (~ (x1 x2))).
Definition term142 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := or ((fun y0 : type1223 a0 a1 => exists y1 : prod a1 a0, (y0 y1) /\ (forall y2 : a1, forall y3 : a0, ~ (y0 (@pair a1 a0 y2 y3)))) x0).
Definition term153 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (exists y0 : prod a1 a0, (fun y1 : prod a1 a0 => (x0 y1) /\ (forall y2 : a1, forall y3 : a0, ~ (x0 (@pair a1 a0 y2 y3)))) y0) \/ (exists y0 : a1, exists y1 : a0, (forall y2 : prod a1 a0, ~ (x0 y2)) /\ (x0 (@pair a1 a0 y0 y1))).
Definition term168 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := fun y0 : prod a1 a0 => ((x0 y0) /\ (forall y1 : a1, forall y2 : a0, ~ (x0 (@pair a1 a0 y1 y2)))) \/ (exists y1 : a1, exists y2 : a0, (forall y3 : prod a1 a0, ~ (x0 y3)) /\ (x0 (@pair a1 a0 y1 y2))).
Definition term50 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := and (~ (exists y0 : prod a1 a0, x0 y0)).
Definition term250 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : prod a1 a0) (x2 : prod a1 a0) := (~ (x0 x1)) \/ (~ (x1 = x2)).
Definition term234 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : prod a1 a0) (x2 : prod a1 a0) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term3 (a0 : Type') (a1 : Type') := ~ (forall y0 : type1223 a0 a1, (exists y1 : prod a1 a0, y0 y1) = (exists y1 : a1, exists y2 : a0, y0 (@pair a1 a0 y1 y2))).
Definition term71 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term53 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (forall y0 : prod a1 a0, ~ (x0 y0)) /\ (exists y0 : a1, exists y1 : a0, x0 (@pair a1 a0 y0 y1)).
Definition term9 (a0 : Type') (a1 : Type') := (forall y0 : prod a1 a0, (@pair a1 a0 (@fst a1 a0 y0) (@snd a1 a0 y0)) = y0) -> False.
Definition term47 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := fun y0 : a1 => ~ ((fun y1 : a1 => exists y2 : a0, x0 (@pair a1 a0 y1 y2)) y0).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) := ~ (ex x0).
Definition term190 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) (x2 : a1) := @eq Prop (((x1 x0) /\ (forall y0 : a1, forall y1 : a0, ~ (x1 (@pair a1 a0 y0 y1)))) \/ (exists y0 : a0, (forall y1 : prod a1 a0, ~ (x1 y1)) /\ (x1 (@pair a1 a0 x2 y0)))).
Definition term189 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) (x2 : a1) := @eq Prop (((x1 x0) /\ (forall y0 : a1, forall y1 : a0, ~ (x1 (@pair a1 a0 y0 y1)))) \/ (exists y0 : a0, (fun y1 : a0 => (forall y2 : prod a1 a0, ~ (x1 y2)) /\ (x1 (@pair a1 a0 x2 y1))) y0)).
Definition term178 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) := @eq Prop (((x1 x0) /\ (forall y0 : a1, forall y1 : a0, ~ (x1 (@pair a1 a0 y0 y1)))) \/ (exists y0 : a1, exists y1 : a0, (forall y2 : prod a1 a0, ~ (x1 y2)) /\ (x1 (@pair a1 a0 y0 y1)))).
Definition term177 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) := @eq Prop (((x1 x0) /\ (forall y0 : a1, forall y1 : a0, ~ (x1 (@pair a1 a0 y0 y1)))) \/ (exists y0 : a1, (fun y1 : a1 => exists y2 : a0, (forall y3 : prod a1 a0, ~ (x1 y3)) /\ (x1 (@pair a1 a0 y1 y2))) y0)).
Definition term15 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) (x2 : a0) := x0 (@pair a1 a0 x1 x2).
Definition term18 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := fun y0 : a1 => exists y1 : a0, x0 (@pair a1 a0 y0 y1).
Definition term93 (a0 : Type') (a1 : Type') := (exists y0 : type1223 a0 a1, (exists y1 : prod a1 a0, y0 y1) /\ (forall y1 : a1, forall y2 : a0, ~ (y0 (@pair a1 a0 y1 y2)))) \/ (exists y0 : type1223 a0 a1, (forall y1 : prod a1 a0, ~ (y0 y1)) /\ (exists y1 : a1, exists y2 : a0, y0 (@pair a1 a0 y1 y2))).
Definition term118 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) := exists y0 : a0, (fun y1 : a0 => x0 (@pair a1 a0 x1 y1)) y0.
Definition term103 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term10 (a0 : Type') (a1 : Type') := ~ (forall y0 : prod a1 a0, (@pair a1 a0 (@fst a1 a0 y0) (@snd a1 a0 y0)) = y0).
Definition term20 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := fun y0 : prod a1 a0 => x0 y0.
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term149 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term240 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : prod a1 a0) (x2 : prod a1 a0) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term49 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : a1, forall y1 : a0, ~ (x0 (@pair a1 a0 y0 y1)).
Definition term169 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := exists y0 : prod a1 a0, ((x0 y0) /\ (forall y1 : a1, forall y2 : a0, ~ (x0 (@pair a1 a0 y1 y2)))) \/ (exists y1 : a1, exists y2 : a0, (forall y3 : prod a1 a0, ~ (x0 y3)) /\ (x0 (@pair a1 a0 y1 y2))).
Definition term251 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : prod a1 a0) := or (x0 x1).
Definition term99 (a0 : Type') (a1 : Type') := fun y0 : type1223 a0 a1 => exists y1 : prod a1 a0, (y0 y1) /\ (forall y2 : a1, forall y3 : a0, ~ (y0 (@pair a1 a0 y2 y3))).
Definition term220 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : prod a1 a0) (x2 : prod a1 a0) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term204 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) := (fun y0 : a1 => forall y1 : a0, ~ (x0 (@pair a1 a0 y0 y1))) x1.
Definition term228 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term101 (a0 : Type') (a1 : Type') := or (exists y0 : type1223 a0 a1, exists y1 : prod a1 a0, (y0 y1) /\ (forall y2 : a1, forall y3 : a0, ~ (y0 (@pair a1 a0 y2 y3)))).
Definition term87 (a0 : Type') (a1 : Type') := exists y0 : type1223 a0 a1, (exists y1 : prod a1 a0, y0 y1) /\ (forall y1 : a1, forall y2 : a0, ~ (y0 (@pair a1 a0 y1 y2))).
Definition term176 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := exists y0 : a1, (fun y1 : a1 => exists y2 : a0, (forall y3 : prod a1 a0, ~ (x0 y3)) /\ (x0 (@pair a1 a0 y1 y2))) y0.
Definition term107 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := exists y0 : a1, (fun y1 : a1 => exists y2 : a0, x0 (@pair a1 a0 y1 y2)) y0.
Definition term151 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : Prop) := (exists y0 : prod a1 a0, x0 y0) \/ x1.
Definition term201 (a0 : Type') (a1 : Type') := exists y0 : type1223 a0 a1, exists y1 : prod a1 a0, exists y2 : a1, exists y3 : a0, ((y0 y1) /\ (forall y4 : a1, forall y5 : a0, ~ (y0 (@pair a1 a0 y4 y5)))) \/ ((forall y4 : prod a1 a0, ~ (y0 y4)) /\ (y0 (@pair a1 a0 y2 y3))).
Definition term102 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term198 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := fun y0 : prod a1 a0 => exists y1 : a1, exists y2 : a0, ((x0 y0) /\ (forall y3 : a1, forall y4 : a0, ~ (x0 (@pair a1 a0 y3 y4)))) \/ ((forall y3 : prod a1 a0, ~ (x0 y3)) /\ (x0 (@pair a1 a0 y1 y2))).
Definition term148 (a0 : Type') (a1 : Type') := exists y0 : type1223 a0 a1, (exists y1 : prod a1 a0, (y0 y1) /\ (forall y2 : a1, forall y3 : a0, ~ (y0 (@pair a1 a0 y2 y3)))) \/ (exists y1 : a1, exists y2 : a0, (forall y3 : prod a1 a0, ~ (y0 y3)) /\ (y0 (@pair a1 a0 y1 y2))).
Definition term216 (x0 : Prop) := (~ x0) -> x0.
Definition term29 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : prod a1 a0) := ~ ((fun y0 : prod a1 a0 => x0 y0) x1).
Definition term28 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : prod a1 a0) := (fun y0 : prod a1 a0 => x0 y0) x1.
Definition term165 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) := ((fun y0 : prod a1 a0 => (x1 y0) /\ (forall y1 : a1, forall y2 : a0, ~ (x1 (@pair a1 a0 y1 y2)))) x0) \/ (exists y0 : a1, exists y1 : a0, (forall y2 : prod a1 a0, ~ (x1 y2)) /\ (x1 (@pair a1 a0 y0 y1))).
Definition term230 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : prod a1 a0) (x2 : prod a1 a0) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term271 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) (x2 : a0) := (~ (x0 (@pair a1 a0 x1 x2))) -> x0 (@pair a1 a0 x1 x2).
Definition term166 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) := ((x1 x0) /\ (forall y0 : a1, forall y1 : a0, ~ (x1 (@pair a1 a0 y0 y1)))) \/ (exists y0 : a1, exists y1 : a0, (forall y2 : prod a1 a0, ~ (x1 y2)) /\ (x1 (@pair a1 a0 y0 y1))).
Definition term267 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : prod a1 a0) := ~ (x0 (@pair a1 a0 (@fst a1 a0 x1) (@snd a1 a0 x1))).
Definition term232 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term159 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := exists y0 : prod a1 a0, (fun y1 : prod a1 a0 => (x0 y1) /\ (forall y2 : a1, forall y3 : a0, ~ (x0 (@pair a1 a0 y2 y3)))) y0.
Definition term226 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : prod a1 a0) (x2 : prod a1 a0) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term97 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : Prop) := exists y0 : prod a1 a0, (x0 y0) /\ x1.
Definition term203 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) := (fun y0 : prod a1 a0 => (@pair a1 a0 (@fst a1 a0 y0) (@snd a1 a0 y0)) = y0) x0.
Definition term173 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) := exists y0 : a1, ((x1 x0) /\ (forall y1 : a1, forall y2 : a0, ~ (x1 (@pair a1 a0 y1 y2)))) \/ ((fun y1 : a1 => exists y2 : a0, (forall y3 : prod a1 a0, ~ (x1 y3)) /\ (x1 (@pair a1 a0 y1 y2))) y0).
Definition term227 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : prod a1 a0) (x2 : prod a1 a0) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term202 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : prod a1 a0) := and (x0 x1).
Definition term124 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) := fun y0 : a0 => (forall y1 : prod a1 a0, ~ (x0 y1)) /\ (x0 (@pair a1 a0 x1 y0)).
Definition term92 (a0 : Type') (a1 : Type') := exists y0 : type1223 a0 a1, (forall y1 : prod a1 a0, ~ (y0 y1)) /\ (exists y1 : a1, exists y2 : a0, y0 (@pair a1 a0 y1 y2)).
Definition term224 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term221 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : prod a1 a0) := ~ (x0 = x1).
Definition term78 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (fun y0 : type1223 a0 a1 => (exists y1 : prod a1 a0, y0 y1) /\ (forall y1 : a1, forall y2 : a0, ~ (y0 (@pair a1 a0 y1 y2)))) x0.
Definition term262 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) (x2 : prod a1 a0) := ((x0 = x2) /\ (x1 x0)) -> x1 x2.
Definition term144 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := ((fun y0 : type1223 a0 a1 => exists y1 : prod a1 a0, (y0 y1) /\ (forall y2 : a1, forall y3 : a0, ~ (y0 (@pair a1 a0 y2 y3)))) x0) \/ ((fun y0 : type1223 a0 a1 => exists y1 : a1, exists y2 : a0, (forall y3 : prod a1 a0, ~ (y0 y3)) /\ (y0 (@pair a1 a0 y1 y2))) x0).
Definition term187 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) := fun y0 : a0 => (fun y1 : a0 => (forall y2 : prod a1 a0, ~ (x0 y2)) /\ (x0 (@pair a1 a0 x1 y1))) y0.
Definition term77 (a0 : Type') (a1 : Type') := fun y0 : type1223 a0 a1 => (forall y1 : prod a1 a0, ~ (y0 y1)) /\ (exists y1 : a1, exists y2 : a0, y0 (@pair a1 a0 y1 y2)).
Definition term138 (a0 : Type') (a1 : Type') := fun y0 : type1223 a0 a1 => (fun y1 : type1223 a0 a1 => exists y2 : a1, exists y3 : a0, (forall y4 : prod a1 a0, ~ (y1 y4)) /\ (y1 (@pair a1 a0 y2 y3))) y0.
Definition term134 (a0 : Type') (a1 : Type') := fun y0 : type1223 a0 a1 => (fun y1 : type1223 a0 a1 => exists y2 : prod a1 a0, (y1 y2) /\ (forall y3 : a1, forall y4 : a0, ~ (y1 (@pair a1 a0 y3 y4)))) y0.
Definition term146 (a0 : Type') (a1 : Type') := fun y0 : type1223 a0 a1 => ((fun y1 : type1223 a0 a1 => exists y2 : prod a1 a0, (y1 y2) /\ (forall y3 : a1, forall y4 : a0, ~ (y1 (@pair a1 a0 y3 y4)))) y0) \/ ((fun y1 : type1223 a0 a1 => exists y2 : a1, exists y3 : a0, (forall y4 : prod a1 a0, ~ (y1 y4)) /\ (y1 (@pair a1 a0 y2 y3))) y0).
Definition term188 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) := exists y0 : a0, (fun y1 : a0 => (forall y2 : prod a1 a0, ~ (x0 y2)) /\ (x0 (@pair a1 a0 x1 y1))) y0.
Definition term19 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := exists y0 : a1, exists y1 : a0, x0 (@pair a1 a0 y0 y1).
Definition term158 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := fun y0 : prod a1 a0 => (fun y1 : prod a1 a0 => (x0 y1) /\ (forall y2 : a1, forall y3 : a0, ~ (x0 (@pair a1 a0 y2 y3)))) y0.
Definition term58 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := or ((exists y0 : prod a1 a0, x0 y0) /\ (forall y0 : a1, forall y1 : a0, ~ (x0 (@pair a1 a0 y0 y1)))).
Definition term197 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) := exists y0 : a1, exists y1 : a0, ((x1 x0) /\ (forall y2 : a1, forall y3 : a0, ~ (x1 (@pair a1 a0 y2 y3)))) \/ ((forall y2 : prod a1 a0, ~ (x1 y2)) /\ (x1 (@pair a1 a0 y0 y1))).
Definition term127 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := exists y0 : a1, exists y1 : a0, (forall y2 : prod a1 a0, ~ (x0 y2)) /\ (x0 (@pair a1 a0 y0 y1)).
Definition term260 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) (x2 : prod a1 a0) := imp (~ ((~ (x2 = x0)) \/ (~ (x1 x2)))).
Definition term209 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) (x2 : prod a1 a0) := (x1 x0) \/ (~ (x1 x2)).
Definition term213 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : prod a1 a0) (x2 : prod a1 a0) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term79 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := or ((fun y0 : type1223 a0 a1 => (exists y1 : prod a1 a0, y0 y1) /\ (forall y1 : a1, forall y2 : a0, ~ (y0 (@pair a1 a0 y1 y2)))) x0).
Definition term229 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : prod a1 a0) (x2 : prod a1 a0) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term210 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) (x2 : prod a1 a0) := (x2 = x0) -> (x1 x0) \/ (~ (x1 x2)).
Definition term139 (a0 : Type') (a1 : Type') := exists y0 : type1223 a0 a1, (fun y1 : type1223 a0 a1 => exists y2 : a1, exists y3 : a0, (forall y4 : prod a1 a0, ~ (y1 y4)) /\ (y1 (@pair a1 a0 y2 y3))) y0.
Definition term135 (a0 : Type') (a1 : Type') := exists y0 : type1223 a0 a1, (fun y1 : type1223 a0 a1 => exists y2 : prod a1 a0, (y1 y2) /\ (forall y3 : a1, forall y4 : a0, ~ (y1 (@pair a1 a0 y3 y4)))) y0.
Definition term113 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := fun y0 : a1 => (forall y1 : prod a1 a0, ~ (x0 y1)) /\ (exists y1 : a0, x0 (@pair a1 a0 y0 y1)).
Definition term199 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := exists y0 : prod a1 a0, exists y1 : a1, exists y2 : a0, ((x0 y0) /\ (forall y3 : a1, forall y4 : a0, ~ (x0 (@pair a1 a0 y3 y4)))) \/ ((forall y3 : prod a1 a0, ~ (x0 y3)) /\ (x0 (@pair a1 a0 y1 y2))).
Definition term37 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) (x2 : a0) := (fun y0 : a0 => x0 (@pair a1 a0 x1 y0)) x2.
Definition term125 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) := exists y0 : a0, (forall y1 : prod a1 a0, ~ (x0 y1)) /\ (x0 (@pair a1 a0 x1 y0)).
Definition term269 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : prod a1 a0) := (x0 (@pair a1 a0 (@fst a1 a0 x1) (@snd a1 a0 x1))) -> False.
Definition term14 (a0 : Type') (a1 : Type') := fun y0 : prod a1 a0 => (@pair a1 a0 (@fst a1 a0 y0) (@snd a1 a0 y0)) = y0.
Definition term7 (a0 : Type') (a1 : Type') := (((~ (forall y0 : type1223 a0 a1, (exists y1 : prod a1 a0, y0 y1) = (exists y1 : a1, exists y2 : a0, y0 (@pair a1 a0 y1 y2)))) -> (forall y0 : prod a1 a0, (@pair a1 a0 (@fst a1 a0 y0) (@snd a1 a0 y0)) = y0) -> False) -> (~ (forall y0 : type1223 a0 a1, (exists y1 : prod a1 a0, y0 y1) = (exists y1 : a1, exists y2 : a0, y0 (@pair a1 a0 y1 y2)))) -> (forall y0 : prod a1 a0, (@pair a1 a0 (@fst a1 a0 y0) (@snd a1 a0 y0)) = y0) -> False) -> (~ (forall y0 : type1223 a0 a1, (exists y1 : prod a1 a0, y0 y1) = (exists y1 : a1, exists y2 : a0, y0 (@pair a1 a0 y1 y2)))) -> (forall y0 : prod a1 a0, (@pair a1 a0 (@fst a1 a0 y0) (@snd a1 a0 y0)) = y0) -> False.
Definition term34 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term130 (a0 : Type') (a1 : Type') := (exists y0 : type1223 a0 a1, exists y1 : prod a1 a0, (y0 y1) /\ (forall y2 : a1, forall y3 : a0, ~ (y0 (@pair a1 a0 y2 y3)))) \/ (exists y0 : type1223 a0 a1, exists y1 : a1, exists y2 : a0, (forall y3 : prod a1 a0, ~ (y0 y3)) /\ (y0 (@pair a1 a0 y1 y2))).
Definition term185 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) (x2 : a1) := exists y0 : a0, ((x1 x0) /\ (forall y1 : a1, forall y2 : a0, ~ (x1 (@pair a1 a0 y1 y2)))) \/ ((fun y1 : a0 => (forall y2 : prod a1 a0, ~ (x1 y2)) /\ (x1 (@pair a1 a0 x2 y1))) y0).
Definition term133 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (fun y0 : type1223 a0 a1 => exists y1 : prod a1 a0, (y0 y1) /\ (forall y2 : a1, forall y3 : a0, ~ (y0 (@pair a1 a0 y2 y3)))) x0.
Definition term171 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term111 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) := (forall y0 : prod a1 a0, ~ (x0 y0)) /\ (exists y0 : a0, x0 (@pair a1 a0 x1 y0)).
Definition term82 (a0 : Type') (a1 : Type') := fun y0 : type1223 a0 a1 => ((fun y1 : type1223 a0 a1 => (exists y2 : prod a1 a0, y1 y2) /\ (forall y2 : a1, forall y3 : a0, ~ (y1 (@pair a1 a0 y2 y3)))) y0) \/ ((fun y1 : type1223 a0 a1 => (forall y2 : prod a1 a0, ~ (y1 y2)) /\ (exists y2 : a1, exists y3 : a0, y1 (@pair a1 a0 y2 y3))) y0).
Definition term217 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) := (~ ((@pair a1 a0 (@fst a1 a0 x0) (@snd a1 a0 x0)) = (@pair a1 a0 (@fst a1 a0 x0) (@snd a1 a0 x0)))) -> (@pair a1 a0 (@fst a1 a0 x0) (@snd a1 a0 x0)) = (@pair a1 a0 (@fst a1 a0 x0) (@snd a1 a0 x0)).
Definition term231 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term246 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) := ~ (x0 = (@pair a1 a0 (@fst a1 a0 x0) (@snd a1 a0 x0))).
Definition term46 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) := ~ ((fun y0 : a1 => exists y1 : a0, x0 (@pair a1 a0 y0 y1)) x1).
Definition term131 (a0 : Type') (a1 : Type') := (exists y0 : type1223 a0 a1, (fun y1 : type1223 a0 a1 => exists y2 : prod a1 a0, (y1 y2) /\ (forall y3 : a1, forall y4 : a0, ~ (y1 (@pair a1 a0 y3 y4)))) y0) \/ (exists y0 : type1223 a0 a1, (fun y1 : type1223 a0 a1 => exists y2 : a1, exists y3 : a0, (forall y4 : prod a1 a0, ~ (y1 y4)) /\ (y1 (@pair a1 a0 y2 y3))) y0).
Definition term75 (a0 : Type') (a1 : Type') := (exists y0 : type1223 a0 a1, (fun y1 : type1223 a0 a1 => (exists y2 : prod a1 a0, y1 y2) /\ (forall y2 : a1, forall y3 : a0, ~ (y1 (@pair a1 a0 y2 y3)))) y0) \/ (exists y0 : type1223 a0 a1, (fun y1 : type1223 a0 a1 => (forall y2 : prod a1 a0, ~ (y1 y2)) /\ (exists y2 : a1, exists y3 : a0, y1 (@pair a1 a0 y2 y3))) y0).
Definition term170 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term95 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term24 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := ~ (ex x0).
Definition term48 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := fun y0 : a1 => forall y1 : a0, ~ (x0 (@pair a1 a0 y0 y1)).
Definition term195 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) (x2 : a1) := exists y0 : a0, ((x1 x0) /\ (forall y1 : a1, forall y2 : a0, ~ (x1 (@pair a1 a0 y1 y2)))) \/ ((forall y1 : prod a1 a0, ~ (x1 y1)) /\ (x1 (@pair a1 a0 x2 y0))).
Definition term73 (a0 : Type') (a1 : Type') (x0 : type330 a0 a1) (x1 : type330 a0 a1) := (exists y0 : type1223 a0 a1, x0 y0) \/ (exists y0 : type1223 a0 a1, x1 y0).
Definition term252 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : prod a1 a0) (x2 : prod a1 a0) := (x0 x2) \/ ((~ (x0 x1)) \/ (~ (x1 = x2))).
Definition term143 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := or (exists y0 : prod a1 a0, (x0 y0) /\ (forall y1 : a1, forall y2 : a0, ~ (x0 (@pair a1 a0 y1 y2)))).
Definition term183 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) := exists y0 : a1, ((x1 x0) /\ (forall y1 : a1, forall y2 : a0, ~ (x1 (@pair a1 a0 y1 y2)))) \/ (exists y1 : a0, (forall y2 : prod a1 a0, ~ (x1 y2)) /\ (x1 (@pair a1 a0 y0 y1))).
Definition term253 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) (x2 : prod a1 a0) := @eq Prop ((~ (x2 = x0)) \/ ((x1 x0) \/ (~ (x1 x2)))).
Definition term239 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : prod a1 a0) (x2 : prod a1 a0) := (x1 = x0) /\ (x1 = x2).
Definition term137 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (fun y0 : type1223 a0 a1 => exists y1 : a1, exists y2 : a0, (forall y3 : prod a1 a0, ~ (y0 y3)) /\ (y0 (@pair a1 a0 y1 y2))) x0.
Definition term150 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term243 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) := ((@pair a1 a0 (@fst a1 a0 x0) (@snd a1 a0 x0)) = x0) /\ ((@pair a1 a0 (@fst a1 a0 x0) (@snd a1 a0 x0)) = (@pair a1 a0 (@fst a1 a0 x0) (@snd a1 a0 x0))).
Definition term39 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) (x2 : a0) := ~ (x0 (@pair a1 a0 x1 x2)).
Definition term116 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) := exists y0 : a0, (forall y1 : prod a1 a0, ~ (x0 y1)) /\ ((fun y1 : a0 => x0 (@pair a1 a0 x1 y1)) y0).
Definition term219 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : prod a1 a0) (x2 : prod a1 a0) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term212 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) (x2 : prod a1 a0) := (~ (x2 = x0)) \/ ((x1 x0) \/ (~ (x1 x2))).
Definition term248 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) (x2 : prod a1 a0) := (x1 x0) \/ ((~ (x2 = x0)) \/ (~ (x1 x2))).
Definition term80 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (fun y0 : type1223 a0 a1 => (forall y1 : prod a1 a0, ~ (y0 y1)) /\ (exists y1 : a1, exists y2 : a0, y0 (@pair a1 a0 y1 y2))) x0.
Definition term67 (a0 : Type') (a1 : Type') := fun y0 : type1223 a0 a1 => ~ ((fun y1 : type1223 a0 a1 => (exists y2 : prod a1 a0, y1 y2) = (exists y2 : a1, exists y3 : a0, y1 (@pair a1 a0 y2 y3))) y0).
Definition term2 (a0 : Type') (a1 : Type') := (~ (forall y0 : type1223 a0 a1, (exists y1 : prod a1 a0, y0 y1) = (exists y1 : a1, exists y2 : a0, y0 (@pair a1 a0 y1 y2)))) -> False.
Definition term163 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : prod a1 a0) := or ((fun y0 : prod a1 a0 => (x0 y0) /\ (forall y1 : a1, forall y2 : a0, ~ (x0 (@pair a1 a0 y1 y2)))) x1).
Definition term193 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) (x2 : a1) := fun y0 : a0 => ((x1 x0) /\ (forall y1 : a1, forall y2 : a0, ~ (x1 (@pair a1 a0 y1 y2)))) \/ ((fun y1 : a0 => (forall y2 : prod a1 a0, ~ (x1 y2)) /\ (x1 (@pair a1 a0 x2 y1))) y0).
Definition term247 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : prod a1 a0) := (~ (x0 x1)) -> x0 x1.
Definition term72 (a0 : Type') (a1 : Type') (x0 : type330 a0 a1) (x1 : type330 a0 a1) := exists y0 : type1223 a0 a1, (x0 y0) \/ (x1 y0).
Definition term258 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : prod a1 a0) := ~ (~ (x0 x1)).
Definition term223 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : prod a1 a0) (x2 : prod a1 a0) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term152 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : Prop) := exists y0 : prod a1 a0, (x0 y0) \/ x1.
Definition term22 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := @eq Prop (exists y0 : prod a1 a0, x0 y0).
Definition term192 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) (x2 : a1) (x3 : a0) := ((x1 x0) /\ (forall y0 : a1, forall y1 : a0, ~ (x1 (@pair a1 a0 y0 y1)))) \/ ((forall y0 : prod a1 a0, ~ (x1 y0)) /\ (x1 (@pair a1 a0 x2 x3))).
Definition term17 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) := exists y0 : a0, x0 (@pair a1 a0 x1 y0).
Definition term145 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (exists y0 : prod a1 a0, (x0 y0) /\ (forall y1 : a1, forall y2 : a0, ~ (x0 (@pair a1 a0 y1 y2)))) \/ (exists y0 : a1, exists y1 : a0, (forall y2 : prod a1 a0, ~ (x0 y2)) /\ (x0 (@pair a1 a0 y0 y1))).
Definition term237 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : prod a1 a0) := and (~ (~ (x0 = x1))).
Definition term225 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : prod a1 a0) (x2 : prod a1 a0) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term129 (a0 : Type') (a1 : Type') := exists y0 : type1223 a0 a1, exists y1 : a1, exists y2 : a0, (forall y3 : prod a1 a0, ~ (y0 y3)) /\ (y0 (@pair a1 a0 y1 y2)).
Definition term244 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) := (((@pair a1 a0 (@fst a1 a0 x0) (@snd a1 a0 x0)) = x0) /\ ((@pair a1 a0 (@fst a1 a0 x0) (@snd a1 a0 x0)) = (@pair a1 a0 (@fst a1 a0 x0) (@snd a1 a0 x0)))) -> x0 = (@pair a1 a0 (@fst a1 a0 x0) (@snd a1 a0 x0)).
Definition term164 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) := or ((x1 x0) /\ (forall y0 : a1, forall y1 : a0, ~ (x1 (@pair a1 a0 y0 y1)))).
Definition term184 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) (x2 : a1) := ((x1 x0) /\ (forall y0 : a1, forall y1 : a0, ~ (x1 (@pair a1 a0 y0 y1)))) \/ (exists y0 : a0, (fun y1 : a0 => (forall y2 : prod a1 a0, ~ (x1 y2)) /\ (x1 (@pair a1 a0 x2 y1))) y0).
Definition term122 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) (x2 : a0) := (forall y0 : prod a1 a0, ~ (x0 y0)) /\ (x0 (@pair a1 a0 x1 x2)).
Definition term207 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term4 (a0 : Type') (a1 : Type') := forall y0 : prod a1 a0, (@pair a1 a0 (@fst a1 a0 y0) (@snd a1 a0 y0)) = y0.
Definition term154 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := exists y0 : prod a1 a0, ((fun y1 : prod a1 a0 => (x0 y1) /\ (forall y2 : a1, forall y3 : a0, ~ (x0 (@pair a1 a0 y2 y3)))) y0) \/ (exists y1 : a1, exists y2 : a0, (forall y3 : prod a1 a0, ~ (x0 y3)) /\ (x0 (@pair a1 a0 y1 y2))).
Definition term255 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) (x2 : prod a1 a0) := (~ ((~ (x0 = x2)) \/ (~ (x1 x0)))) -> x1 x2.
Definition term83 (a0 : Type') (a1 : Type') := @eq Prop (exists y0 : type1223 a0 a1, ((fun y1 : type1223 a0 a1 => (exists y2 : prod a1 a0, y1 y2) /\ (forall y2 : a1, forall y3 : a0, ~ (y1 (@pair a1 a0 y2 y3)))) y0) \/ ((fun y1 : type1223 a0 a1 => (forall y2 : prod a1 a0, ~ (y1 y2)) /\ (exists y2 : a1, exists y3 : a0, y1 (@pair a1 a0 y2 y3))) y0)).
Definition term254 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : prod a1 a0) (x2 : prod a1 a0) := @eq Prop ((x0 x2) \/ ((~ (x0 x1)) \/ (~ (x1 = x2)))).
Definition term55 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (exists y0 : prod a1 a0, x0 y0) /\ (~ (exists y0 : a1, exists y1 : a0, x0 (@pair a1 a0 y0 y1))).
Definition term60 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := ((exists y0 : prod a1 a0, x0 y0) /\ (forall y0 : a1, forall y1 : a0, ~ (x0 (@pair a1 a0 y0 y1)))) \/ ((forall y0 : prod a1 a0, ~ (x0 y0)) /\ (exists y0 : a1, exists y1 : a0, x0 (@pair a1 a0 y0 y1))).
Definition term96 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : Prop) := (exists y0 : prod a1 a0, x0 y0) /\ x1.
Definition term21 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := exists y0 : prod a1 a0, x0 y0.
Definition term259 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) (x2 : prod a1 a0) := (x2 = x0) /\ (x1 x2).
Definition term155 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := fun y0 : prod a1 a0 => (x0 y0) /\ (forall y1 : a1, forall y2 : a0, ~ (x0 (@pair a1 a0 y1 y2))).
Definition term123 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) := fun y0 : a0 => (forall y1 : prod a1 a0, ~ (x0 y1)) /\ ((fun y1 : a0 => x0 (@pair a1 a0 x1 y1)) y0).
Definition term16 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) := fun y0 : a0 => x0 (@pair a1 a0 x1 y0).
Definition term245 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) := (~ (x0 = (@pair a1 a0 (@fst a1 a0 x0) (@snd a1 a0 x0)))) -> x0 = (@pair a1 a0 (@fst a1 a0 x0) (@snd a1 a0 x0)).
Definition term76 (a0 : Type') (a1 : Type') := fun y0 : type1223 a0 a1 => (exists y1 : prod a1 a0, y0 y1) /\ (forall y1 : a1, forall y2 : a0, ~ (y0 (@pair a1 a0 y1 y2))).
Definition term98 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := exists y0 : prod a1 a0, (x0 y0) /\ (forall y1 : a1, forall y2 : a0, ~ (x0 (@pair a1 a0 y1 y2))).
Definition term32 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := fun y0 : prod a1 a0 => ~ (x0 y0).
Definition term238 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : prod a1 a0) := and (x0 = x1).
Definition term175 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := fun y0 : a1 => (fun y1 : a1 => exists y2 : a0, (forall y3 : prod a1 a0, ~ (x0 y3)) /\ (x0 (@pair a1 a0 y1 y2))) y0.
Definition term31 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := fun y0 : prod a1 a0 => ~ ((fun y1 : prod a1 a0 => x0 y1) y0).
Definition term167 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := fun y0 : prod a1 a0 => ((fun y1 : prod a1 a0 => (x0 y1) /\ (forall y2 : a1, forall y3 : a0, ~ (x0 (@pair a1 a0 y2 y3)))) y0) \/ (exists y1 : a1, exists y2 : a0, (forall y3 : prod a1 a0, ~ (x0 y3)) /\ (x0 (@pair a1 a0 y1 y2))).
Definition term180 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) (x2 : a1) := ((x1 x0) /\ (forall y0 : a1, forall y1 : a0, ~ (x1 (@pair a1 a0 y0 y1)))) \/ (exists y0 : a0, (forall y1 : prod a1 a0, ~ (x1 y1)) /\ (x1 (@pair a1 a0 x2 y0))).
Definition term136 (a0 : Type') (a1 : Type') := or (exists y0 : type1223 a0 a1, (fun y1 : type1223 a0 a1 => exists y2 : prod a1 a0, (y1 y2) /\ (forall y3 : a1, forall y4 : a0, ~ (y1 (@pair a1 a0 y3 y4)))) y0).
Definition term88 (a0 : Type') (a1 : Type') := or (exists y0 : type1223 a0 a1, (fun y1 : type1223 a0 a1 => (exists y2 : prod a1 a0, y1 y2) /\ (forall y2 : a1, forall y3 : a0, ~ (y1 (@pair a1 a0 y2 y3)))) y0).
Definition term1 (a0 : Type') (a1 : Type') := forall y0 : type1223 a0 a1, (exists y1 : prod a1 a0, y0 y1) = (exists y1 : a1, exists y2 : a0, y0 (@pair a1 a0 y1 y2)).
Definition term54 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := and (exists y0 : prod a1 a0, x0 y0).
Definition term45 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) := (fun y0 : a1 => exists y1 : a0, x0 (@pair a1 a0 y0 y1)) x1.
Definition term233 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : prod a1 a0) (x2 : prod a1 a0) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term106 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := fun y0 : a1 => (fun y1 : a1 => exists y2 : a0, x0 (@pair a1 a0 y1 y2)) y0.
Definition term157 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) := (x1 x0) /\ (forall y0 : a1, forall y1 : a0, ~ (x1 (@pair a1 a0 y0 y1))).
Definition term194 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) (x2 : a1) := fun y0 : a0 => ((x1 x0) /\ (forall y1 : a1, forall y2 : a0, ~ (x1 (@pair a1 a0 y1 y2)))) \/ ((forall y1 : prod a1 a0, ~ (x1 y1)) /\ (x1 (@pair a1 a0 x2 y0))).
Definition term12 (a0 : Type') (a1 : Type') := (~ (forall y0 : type1223 a0 a1, (exists y1 : prod a1 a0, y0 y1) = (exists y1 : a1, exists y2 : a0, y0 (@pair a1 a0 y1 y2)))) -> ~ (forall y0 : prod a1 a0, (@pair a1 a0 (@fst a1 a0 y0) (@snd a1 a0 y0)) = y0).
Definition term214 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) := (~ ((@pair a1 a0 (@fst a1 a0 x0) (@snd a1 a0 x0)) = x0)) -> (@pair a1 a0 (@fst a1 a0 x0) (@snd a1 a0 x0)) = x0.
Definition term242 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : prod a1 a0) (x2 : prod a1 a0) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term147 (a0 : Type') (a1 : Type') := fun y0 : type1223 a0 a1 => (exists y1 : prod a1 a0, (y0 y1) /\ (forall y2 : a1, forall y3 : a0, ~ (y0 (@pair a1 a0 y2 y3)))) \/ (exists y1 : a1, exists y2 : a0, (forall y3 : prod a1 a0, ~ (y0 y3)) /\ (y0 (@pair a1 a0 y1 y2))).
Definition term35 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) := ~ (exists y0 : a0, x0 (@pair a1 a0 x1 y0)).
Definition term132 (a0 : Type') (a1 : Type') := exists y0 : type1223 a0 a1, ((fun y1 : type1223 a0 a1 => exists y2 : prod a1 a0, (y1 y2) /\ (forall y3 : a1, forall y4 : a0, ~ (y1 (@pair a1 a0 y3 y4)))) y0) \/ ((fun y1 : type1223 a0 a1 => exists y2 : a1, exists y3 : a0, (forall y4 : prod a1 a0, ~ (y1 y4)) /\ (y1 (@pair a1 a0 y2 y3))) y0).
Definition term74 (a0 : Type') (a1 : Type') := exists y0 : type1223 a0 a1, ((fun y1 : type1223 a0 a1 => (exists y2 : prod a1 a0, y1 y2) /\ (forall y2 : a1, forall y3 : a0, ~ (y1 (@pair a1 a0 y2 y3)))) y0) \/ ((fun y1 : type1223 a0 a1 => (forall y2 : prod a1 a0, ~ (y1 y2)) /\ (exists y2 : a1, exists y3 : a0, y1 (@pair a1 a0 y2 y3))) y0).
Definition term211 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term272 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : prod a1 a0) := (x0 x1) -> False.
Definition term59 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := ((exists y0 : prod a1 a0, x0 y0) /\ (~ (exists y0 : a1, exists y1 : a0, x0 (@pair a1 a0 y0 y1)))) \/ ((~ (exists y0 : prod a1 a0, x0 y0)) /\ (exists y0 : a1, exists y1 : a0, x0 (@pair a1 a0 y0 y1))).
Definition term181 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) := fun y0 : a1 => ((x1 x0) /\ (forall y1 : a1, forall y2 : a0, ~ (x1 (@pair a1 a0 y1 y2)))) \/ ((fun y1 : a1 => exists y2 : a0, (forall y3 : prod a1 a0, ~ (x1 y3)) /\ (x1 (@pair a1 a0 y1 y2))) y0).
Definition term84 (a0 : Type') (a1 : Type') := @eq Prop (exists y0 : type1223 a0 a1, ((exists y1 : prod a1 a0, y0 y1) /\ (forall y1 : a1, forall y2 : a0, ~ (y0 (@pair a1 a0 y1 y2)))) \/ ((forall y1 : prod a1 a0, ~ (y0 y1)) /\ (exists y1 : a1, exists y2 : a0, y0 (@pair a1 a0 y1 y2)))).
Definition term117 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) := fun y0 : a0 => (fun y1 : a0 => x0 (@pair a1 a0 x1 y1)) y0.
Definition term42 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) := forall y0 : a0, ~ (x0 (@pair a1 a0 x1 y0)).
Definition term115 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) := (forall y0 : prod a1 a0, ~ (x0 y0)) /\ (exists y0 : a0, (fun y1 : a0 => x0 (@pair a1 a0 x1 y1)) y0).
Definition term110 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) := (forall y0 : prod a1 a0, ~ (x0 y0)) /\ ((fun y0 : a1 => exists y1 : a0, x0 (@pair a1 a0 y0 y1)) x1).
Definition term120 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) := @eq Prop ((forall y0 : prod a1 a0, ~ (x0 y0)) /\ (exists y0 : a0, x0 (@pair a1 a0 x1 y0))).
Definition term119 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) := @eq Prop ((forall y0 : prod a1 a0, ~ (x0 y0)) /\ (exists y0 : a0, (fun y1 : a0 => x0 (@pair a1 a0 x1 y1)) y0)).
Definition term109 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := @eq Prop ((forall y0 : prod a1 a0, ~ (x0 y0)) /\ (exists y0 : a1, exists y1 : a0, x0 (@pair a1 a0 y0 y1))).
Definition term108 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := @eq Prop ((forall y0 : prod a1 a0, ~ (x0 y0)) /\ (exists y0 : a1, (fun y1 : a1 => exists y2 : a0, x0 (@pair a1 a0 y1 y2)) y0)).
Definition term241 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : prod a1 a0) (x2 : prod a1 a0) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term268 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) (x2 : a0) := (x0 (@pair a1 a0 x1 x2)) -> False.
Definition term186 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) (x2 : a0) := (fun y0 : a0 => (forall y1 : prod a1 a0, ~ (x0 y1)) /\ (x0 (@pair a1 a0 x1 y0))) x2.
Definition term128 (a0 : Type') (a1 : Type') := fun y0 : type1223 a0 a1 => exists y1 : a1, exists y2 : a0, (forall y3 : prod a1 a0, ~ (y0 y3)) /\ (y0 (@pair a1 a0 y1 y2)).
Definition term63 (a0 : Type') (a1 : Type') (x0 : type330 a0 a1) := exists y0 : type1223 a0 a1, ~ (x0 y0).
Definition term56 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (exists y0 : prod a1 a0, x0 y0) /\ (forall y0 : a1, forall y1 : a0, ~ (x0 (@pair a1 a0 y0 y1))).
Definition term266 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : prod a1 a0) := (~ (x0 (@pair a1 a0 (@fst a1 a0 x1) (@snd a1 a0 x1)))) -> x0 (@pair a1 a0 (@fst a1 a0 x1) (@snd a1 a0 x1)).
Definition term44 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : a1, ~ ((fun y1 : a1 => exists y2 : a0, x0 (@pair a1 a0 y1 y2)) y0).
Definition term57 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := or ((exists y0 : prod a1 a0, x0 y0) /\ (~ (exists y0 : a1, exists y1 : a0, x0 (@pair a1 a0 y0 y1)))).
Definition term114 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := exists y0 : a1, (forall y1 : prod a1 a0, ~ (x0 y1)) /\ (exists y1 : a0, x0 (@pair a1 a0 y0 y1)).
Definition term43 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := ~ (exists y0 : a1, exists y1 : a0, x0 (@pair a1 a0 y0 y1)).
Definition term179 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) (x2 : a1) := ((x1 x0) /\ (forall y0 : a1, forall y1 : a0, ~ (x1 (@pair a1 a0 y0 y1)))) \/ ((fun y0 : a1 => exists y1 : a0, (forall y2 : prod a1 a0, ~ (x1 y2)) /\ (x1 (@pair a1 a0 y0 y1))) x2).
Definition term94 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term65 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (fun y0 : type1223 a0 a1 => (exists y1 : prod a1 a0, y0 y1) = (exists y1 : a1, exists y2 : a0, y0 (@pair a1 a0 y1 y2))) x0.
Definition term205 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) (x2 : a0) := (fun y0 : a0 => ~ (x0 (@pair a1 a0 x1 y0))) x2.
Definition term51 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := and (forall y0 : prod a1 a0, ~ (x0 y0)).
Definition term6 (a0 : Type') (a1 : Type') := ((~ (forall y0 : type1223 a0 a1, (exists y1 : prod a1 a0, y0 y1) = (exists y1 : a1, exists y2 : a0, y0 (@pair a1 a0 y1 y2)))) -> (forall y0 : prod a1 a0, (@pair a1 a0 (@fst a1 a0 y0) (@snd a1 a0 y0)) = y0) -> False) -> (~ (forall y0 : type1223 a0 a1, (exists y1 : prod a1 a0, y0 y1) = (exists y1 : a1, exists y2 : a0, y0 (@pair a1 a0 y1 y2)))) -> (forall y0 : prod a1 a0, (@pair a1 a0 (@fst a1 a0 y0) (@snd a1 a0 y0)) = y0) -> False.
Definition term249 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) (x2 : prod a1 a0) := (~ (x2 = x0)) \/ (~ (x1 x2)).
Definition term105 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := exists y0 : a1, (forall y1 : prod a1 a0, ~ (x0 y1)) /\ ((fun y1 : a1 => exists y2 : a0, x0 (@pair a1 a0 y1 y2)) y0).
Definition term236 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : prod a1 a0) := ~ (~ (x0 = x1)).
Definition term27 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : prod a1 a0, ~ ((fun y1 : prod a1 a0 => x0 y1) y0).
Definition term89 (a0 : Type') (a1 : Type') := or (exists y0 : type1223 a0 a1, (exists y1 : prod a1 a0, y0 y1) /\ (forall y1 : a1, forall y2 : a0, ~ (y0 (@pair a1 a0 y1 y2)))).
Definition term8 (a0 : Type') (a1 : Type') := (((~ (forall y0 : type1223 a0 a1, (exists y1 : prod a1 a0, y0 y1) = (exists y1 : a1, exists y2 : a0, y0 (@pair a1 a0 y1 y2)))) -> (forall y0 : prod a1 a0, (@pair a1 a0 (@fst a1 a0 y0) (@snd a1 a0 y0)) = y0) -> False) -> (~ (forall y0 : type1223 a0 a1, (exists y1 : prod a1 a0, y0 y1) = (exists y1 : a1, exists y2 : a0, y0 (@pair a1 a0 y1 y2)))) -> (forall y0 : prod a1 a0, (@pair a1 a0 (@fst a1 a0 y0) (@snd a1 a0 y0)) = y0) -> False) -> ((~ (forall y0 : type1223 a0 a1, (exists y1 : prod a1 a0, y0 y1) = (exists y1 : a1, exists y2 : a0, y0 (@pair a1 a0 y1 y2)))) -> (forall y0 : prod a1 a0, (@pair a1 a0 (@fst a1 a0 y0) (@snd a1 a0 y0)) = y0) -> False) -> (~ (forall y0 : type1223 a0 a1, (exists y1 : prod a1 a0, y0 y1) = (exists y1 : a1, exists y2 : a0, y0 (@pair a1 a0 y1 y2)))) -> (forall y0 : prod a1 a0, (@pair a1 a0 (@fst a1 a0 y0) (@snd a1 a0 y0)) = y0) -> False.
Definition term218 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) := ~ ((@pair a1 a0 (@fst a1 a0 x0) (@snd a1 a0 x0)) = (@pair a1 a0 (@fst a1 a0 x0) (@snd a1 a0 x0))).
Definition term172 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) := ((x1 x0) /\ (forall y0 : a1, forall y1 : a0, ~ (x1 (@pair a1 a0 y0 y1)))) \/ (exists y0 : a1, (fun y1 : a1 => exists y2 : a0, (forall y3 : prod a1 a0, ~ (x1 y3)) /\ (x1 (@pair a1 a0 y1 y2))) y0).
Definition term66 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := ~ ((fun y0 : type1223 a0 a1 => (exists y1 : prod a1 a0, y0 y1) = (exists y1 : a1, exists y2 : a0, y0 (@pair a1 a0 y1 y2))) x0).
Definition term174 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) := (fun y0 : a1 => exists y1 : a0, (forall y2 : prod a1 a0, ~ (x0 y2)) /\ (x0 (@pair a1 a0 y0 y1))) x1.
Definition term222 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : prod a1 a0) := or (~ (x0 = x1)).
Definition term36 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) := forall y0 : a0, ~ ((fun y1 : a0 => x0 (@pair a1 a0 x1 y1)) y0).
Definition term126 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := fun y0 : a1 => exists y1 : a0, (forall y2 : prod a1 a0, ~ (x0 y2)) /\ (x0 (@pair a1 a0 y0 y1)).
Definition term263 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : prod a1 a0) := (x1 = (@pair a1 a0 (@fst a1 a0 x1) (@snd a1 a0 x1))) /\ (x0 x1).
Definition term160 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := or (exists y0 : prod a1 a0, (fun y1 : prod a1 a0 => (x0 y1) /\ (forall y2 : a1, forall y3 : a0, ~ (x0 (@pair a1 a0 y2 y3)))) y0).
Definition term81 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := ((fun y0 : type1223 a0 a1 => (exists y1 : prod a1 a0, y0 y1) /\ (forall y1 : a1, forall y2 : a0, ~ (y0 (@pair a1 a0 y1 y2)))) x0) \/ ((fun y0 : type1223 a0 a1 => (forall y1 : prod a1 a0, ~ (y0 y1)) /\ (exists y1 : a1, exists y2 : a0, y0 (@pair a1 a0 y1 y2))) x0).
Definition term90 (a0 : Type') (a1 : Type') := fun y0 : type1223 a0 a1 => (fun y1 : type1223 a0 a1 => (forall y2 : prod a1 a0, ~ (y1 y2)) /\ (exists y2 : a1, exists y3 : a0, y1 (@pair a1 a0 y2 y3))) y0.
Definition term85 (a0 : Type') (a1 : Type') := fun y0 : type1223 a0 a1 => (fun y1 : type1223 a0 a1 => (exists y2 : prod a1 a0, y1 y2) /\ (forall y2 : a1, forall y3 : a0, ~ (y1 (@pair a1 a0 y2 y3)))) y0.
Definition term70 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term261 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) (x2 : prod a1 a0) := imp ((x2 = x0) /\ (x1 x2)).
Definition term38 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : a1) (x2 : a0) := ~ ((fun y0 : a0 => x0 (@pair a1 a0 x1 y0)) x2).
Definition term23 (a0 : Type') (a1 : Type') := fun y0 : type1223 a0 a1 => (exists y1 : prod a1 a0, y0 y1) = (exists y1 : a1, exists y2 : a0, y0 (@pair a1 a0 y1 y2)).
Definition term200 (a0 : Type') (a1 : Type') := fun y0 : type1223 a0 a1 => exists y1 : prod a1 a0, exists y2 : a1, exists y3 : a0, ((y0 y1) /\ (forall y4 : a1, forall y5 : a0, ~ (y0 (@pair a1 a0 y4 y5)))) \/ ((forall y4 : prod a1 a0, ~ (y0 y4)) /\ (y0 (@pair a1 a0 y2 y3))).
Definition term68 (a0 : Type') (a1 : Type') := fun y0 : type1223 a0 a1 => ((exists y1 : prod a1 a0, y0 y1) /\ (forall y1 : a1, forall y2 : a0, ~ (y0 (@pair a1 a0 y1 y2)))) \/ ((forall y1 : prod a1 a0, ~ (y0 y1)) /\ (exists y1 : a1, exists y2 : a0, y0 (@pair a1 a0 y1 y2))).
Definition term13 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) := @pair a1 a0 (@fst a1 a0 x0) (@snd a1 a0 x0).
Definition term208 (a0 : Type') (a1 : Type') (x0 : prod a1 a0) (x1 : type1223 a0 a1) (x2 : prod a1 a0) := ((x1 x2) = (x1 x0)) -> (x1 x0) \/ (~ (x1 x2)).
Definition term265 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : prod a1 a0) := x0 (@pair a1 a0 (@fst a1 a0 x1) (@snd a1 a0 x1)).
Definition term11 (a0 : Type') (a1 : Type') := imp (~ (forall y0 : type1223 a0 a1, (exists y1 : prod a1 a0, y0 y1) = (exists y1 : a1, exists y2 : a0, y0 (@pair a1 a0 y1 y2)))).
Definition term69 (a0 : Type') (a1 : Type') := exists y0 : type1223 a0 a1, ((exists y1 : prod a1 a0, y0 y1) /\ (forall y1 : a1, forall y2 : a0, ~ (y0 (@pair a1 a0 y1 y2)))) \/ ((forall y1 : prod a1 a0, ~ (y0 y1)) /\ (exists y1 : a1, exists y2 : a0, y0 (@pair a1 a0 y1 y2))).
Definition term30 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : prod a1 a0) := ~ (x0 x1).
Definition term156 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : prod a1 a0) := (fun y0 : prod a1 a0 => (x0 y0) /\ (forall y1 : a1, forall y2 : a0, ~ (x0 (@pair a1 a0 y1 y2)))) x1.
Definition term264 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) (x1 : prod a1 a0) := ((x1 = (@pair a1 a0 (@fst a1 a0 x1) (@snd a1 a0 x1))) /\ (x0 x1)) -> x0 (@pair a1 a0 (@fst a1 a0 x1) (@snd a1 a0 x1)).
Definition term162 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := @eq Prop ((exists y0 : prod a1 a0, (x0 y0) /\ (forall y1 : a1, forall y2 : a0, ~ (x0 (@pair a1 a0 y1 y2)))) \/ (exists y0 : a1, exists y1 : a0, (forall y2 : prod a1 a0, ~ (x0 y2)) /\ (x0 (@pair a1 a0 y0 y1)))).
Definition term161 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := @eq Prop ((exists y0 : prod a1 a0, (fun y1 : prod a1 a0 => (x0 y1) /\ (forall y2 : a1, forall y3 : a0, ~ (x0 (@pair a1 a0 y2 y3)))) y0) \/ (exists y0 : a1, exists y1 : a0, (forall y2 : prod a1 a0, ~ (x0 y2)) /\ (x0 (@pair a1 a0 y0 y1)))).
Definition term141 (a0 : Type') (a1 : Type') := @eq Prop ((exists y0 : type1223 a0 a1, exists y1 : prod a1 a0, (y0 y1) /\ (forall y2 : a1, forall y3 : a0, ~ (y0 (@pair a1 a0 y2 y3)))) \/ (exists y0 : type1223 a0 a1, exists y1 : a1, exists y2 : a0, (forall y3 : prod a1 a0, ~ (y0 y3)) /\ (y0 (@pair a1 a0 y1 y2)))).
Definition term140 (a0 : Type') (a1 : Type') := @eq Prop ((exists y0 : type1223 a0 a1, (fun y1 : type1223 a0 a1 => exists y2 : prod a1 a0, (y1 y2) /\ (forall y3 : a1, forall y4 : a0, ~ (y1 (@pair a1 a0 y3 y4)))) y0) \/ (exists y0 : type1223 a0 a1, (fun y1 : type1223 a0 a1 => exists y2 : a1, exists y3 : a0, (forall y4 : prod a1 a0, ~ (y1 y4)) /\ (y1 (@pair a1 a0 y2 y3))) y0)).
