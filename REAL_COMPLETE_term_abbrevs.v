Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term91 (x0 : Prop) := False -> x0 -> False.
Definition term243 (x0 : real) (x1 : real) (x2 : real) := imp (real_le x0 (real_add x1 (real_neg x2))).
Definition term54 (x0 : real) (x1 : real) := (real_le x0 x1) -> forall y0 : real, real_le (real_add y0 x0) (real_add y0 x1).
Definition term97 (x0 : Prop) (x1 : Prop) := x0 -> (x0 -> False) -> x1.
Definition term82 (x0 : Prop) (x1 : Prop) := x0 -> (x0 -> True) -> x1.
Definition term113 (x0 : Prop) (x1 : Prop) (x2 : Prop) := ((x1 -> x2) -> x0 -> (x0 -> x1) -> x2) -> (x1 -> x2) -> x0 -> (x0 -> x1) -> x2.
Definition term152 (x0 : real) := real_add (real_neg x0) (real_of_num (NUMERAL 0)).
Definition term71 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (y0 -> x1) -> x0 -> (x0 -> y0) -> x1) x2.
Definition term28 (x0 : real) (x1 : real) := real_add x0 (real_neg x1).
Definition term333 (x0 : real) (x1 : real -> Prop) := (forall y0 : real, real_le (real_add y0 x0) (real_add y0 (real_of_num (NUMERAL 0)))) -> exists y0 : real, (forall y1 : real, (x1 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x1 y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term122 (x0 : real -> Prop) := (forall y0 : real -> Prop, ((exists y1 : real, (y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y1)) /\ (exists y1 : real, forall y2 : real, (y0 y2) -> real_le y2 y1)) -> exists y1 : real, (forall y2 : real, (y0 y2) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (y0 y3) -> real_le y3 y2) -> real_le y1 y2)) -> exists y0 : real, (forall y1 : real, (x0 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x0 y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term84 (x0 : Prop) := fun y0 : Prop => y0 -> x0 -> y0.
Definition term181 (x0 : real -> Prop) (x1 : real) (x2 : real) := fun y0 : real => ((fun y1 : real => x0 (real_add y1 x1)) y0) -> real_le y0 x2.
Definition term51 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 x2) -> real_le (real_add x1 x0) (real_add x1 x2).
Definition term36 (x0 : real) := @eq real (real_add x0 (real_of_num (NUMERAL 0))).
Definition term309 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_add (real_add x0 x2) (real_neg x2)) (real_add x1 (real_neg x2))) -> real_le x0 (real_sub x1 x2).
Definition term94 (x0 : Prop) := imp (~ x0).
Definition term180 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real) := (x0 (real_add x2 x1)) -> real_le x2 x3.
Definition term171 (x0 : real -> Prop) (x1 : real) := fun y0 : real => ((fun y1 : real => x0 (real_add y1 x1)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y0).
Definition term98 (x0 : Prop) (x1 : Prop) := x0 -> (~ x0) -> x1.
Definition term219 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real) := (x0 (real_add x1 x2)) -> real_le (real_add x1 x2) x3.
Definition term149 (x0 : real) := real_le (real_add (real_neg x0) x0) (real_add (real_neg x0) (real_of_num (NUMERAL 0))).
Definition term327 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real) := (forall y0 : real, (x0 y0) -> real_le y0 x3) -> real_le (real_add x1 x2) x3.
Definition term135 (x0 : real -> Prop) (x1 : real) := (x0 x1) /\ (real_le (real_of_num (NUMERAL 0)) x1).
Definition term89 (x0 : Prop) (x1 : Prop) := @eq Prop (x1 -> x0 -> x1).
Definition term290 (x0 : real) (x1 : real) (x2 : real) := real_le (real_add x0 (real_add (real_neg x2) (real_add x2 x2))) (real_add x1 x2).
Definition term310 (x0 : real) (x1 : real) (x2 : real) := ((real_le (real_add (real_add x0 x2) (real_neg x2)) (real_add x1 (real_neg x2))) = (real_le x0 (real_add x1 (real_neg x2)))) -> (real_le (real_add (real_add x0 x2) (real_neg x2)) (real_add x1 (real_neg x2))) -> real_le x0 (real_add x1 (real_neg x2)).
Definition term217 := real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term220 (x0 : real) (x1 : real) (x2 : real) := real_le (real_add x0 x1) x2.
Definition term21 := real_of_num (NUMERAL 0).
Definition term114 (x0 : real -> Prop) (x1 : real) := (fun y0 : real -> Prop => ((exists y1 : real, (y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y1)) /\ (exists y1 : real, forall y2 : real, (y0 y2) -> real_le y2 y1)) -> exists y1 : real, (forall y2 : real, (y0 y2) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (y0 y3) -> real_le y3 y2) -> real_le y1 y2)) (fun y0 : real => x0 (real_add y0 x1)).
Definition term167 (x0 : real -> Prop) (x1 : real) (x2 : real) := and ((fun y0 : real => x0 (real_add y0 x1)) x2).
Definition term134 (x0 : real -> Prop) (x1 : real) := and (x0 x1).
Definition term173 (x0 : real -> Prop) (x1 : real) := exists y0 : real, ((fun y1 : real => x0 (real_add y1 x1)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y0).
Definition term229 (x0 : real) (x1 : real) := real_add (real_neg x0) x1.
Definition term164 (x0 : real) (x1 : real -> Prop) := (real_le (real_of_num (NUMERAL 0)) (real_neg x0)) -> exists y0 : real, (forall y1 : real, (x1 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x1 y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term59 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) -> forall y1 : real, real_le (real_add y1 x0) (real_add y1 y0)) x1.
Definition term194 (x0 : real -> Prop) (x1 : real) (x2 : real) := and (forall y0 : real, (x0 (real_add y0 x1)) -> real_le y0 x2).
Definition term193 (x0 : real -> Prop) (x1 : real) (x2 : real) := and (forall y0 : real, ((fun y1 : real => x0 (real_add y1 x1)) y0) -> real_le y0 x2).
Definition term141 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term65 := forall y0 : real, (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0)).
Definition term302 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real) := (forall y0 : real, (forall y1 : real, (x0 (real_add y1 x1)) -> real_le y1 y0) -> real_le x2 y0) -> real_le x2 x3.
Definition term198 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real) := (forall y0 : real, (x0 (real_add y0 x1)) -> real_le y0 x3) -> real_le x2 x3.
Definition term197 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real) := (forall y0 : real, ((fun y1 : real => x0 (real_add y1 x1)) y0) -> real_le y0 x3) -> real_le x2 x3.
Definition term289 (x0 : real) (x1 : real) := real_le (real_add x0 (real_add (real_neg x1) (real_add x1 x1))).
Definition term179 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real) := ((fun y0 : real => x0 (real_add y0 x1)) x2) -> real_le x2 x3.
Definition term107 (x0 : Prop) := False -> (~ False) -> x0.
Definition term38 := fun y0 : real => (real_add y0 (real_of_num (NUMERAL 0))) = y0.
Definition term311 (x0 : real) (x1 : real) := @eq real (real_add (real_add x0 x1) (real_neg x1)).
Definition term293 (x0 : real) (x1 : real) (x2 : real) := imp (real_le (real_add x0 (real_of_num (NUMERAL 0))) (real_add x1 x2)).
Definition term244 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 (real_add x1 (real_neg x2))) -> real_le x0 (real_add x1 (real_neg x2)).
Definition term188 (x0 : real -> Prop) (x1 : real) := exists y0 : real, forall y1 : real, (x0 (real_add y1 x1)) -> real_le y1 y0.
Definition term187 (x0 : real -> Prop) (x1 : real) := exists y0 : real, forall y1 : real, ((fun y2 : real => x0 (real_add y2 x1)) y1) -> real_le y1 y0.
Definition term131 (x0 : real -> Prop) := exists y0 : real, forall y1 : real, (x0 y1) -> real_le y1 y0.
Definition term216 (x0 : real -> Prop) (x1 : real) := and (x0 (real_add (real_of_num (NUMERAL 0)) x1)).
Definition term292 (x0 : real) (x1 : real) (x2 : real) := real_le (real_add x0 (real_of_num (NUMERAL 0))) (real_add x1 x2).
Definition term139 := fun y0 : real => True.
Definition term57 := (forall y0 : real, forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2)) -> forall y0 : real, forall y1 : real, (real_le y0 y1) -> forall y2 : real, real_le (real_add y2 y0) (real_add y2 y1).
Definition term317 (x0 : real) (x1 : real) (x2 : real) := forall y0 : real, real_le (real_add y0 x0) (real_add y0 (real_sub x1 x2)).
Definition term316 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 (real_sub x1 x2)) -> forall y0 : real, real_le (real_add y0 x0) (real_add y0 (real_sub x1 x2)).
Definition term241 (x0 : real) (x1 : real) (x2 : real) := imp (real_le (real_add x0 (real_of_num (NUMERAL 0))) (real_add x1 (real_neg x2))).
Definition term165 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => x0 (real_add y0 x1)) x2.
Definition term330 (x0 : real -> Prop) := fun y0 : real => (forall y1 : real, (x0 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x0 y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term206 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (forall y1 : real, (x0 (real_add y1 x1)) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x0 (real_add y2 x1)) -> real_le y2 y1) -> real_le y0 y1).
Definition term205 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (forall y1 : real, ((fun y2 : real => x0 (real_add y2 x1)) y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, ((fun y3 : real => x0 (real_add y3 x1)) y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term281 (x0 : real) (x1 : real) (x2 : real) := imp (real_le (real_add (real_sub x0 x2) x2) (real_add x1 x2)).
Definition term275 (x0 : real) (x1 : real) (x2 : real) := imp (real_le (real_add (real_add (real_sub x0 x2) x2) x2) (real_add x1 x2)).
Definition term269 (x0 : real) (x1 : real) := real_add x1 (real_add (real_sub x0 x1) x1).
Definition term61 (x0 : real) := @eq real (real_add (real_neg x0) x0).
Definition term184 (x0 : real -> Prop) (x1 : real) (x2 : real) := forall y0 : real, (x0 (real_add y0 x1)) -> real_le y0 x2.
Definition term3 (x0 : real) := forall y0 : real, (real_add x0 y0) = (real_add y0 x0).
Definition term280 (x0 : real) (x1 : real) (x2 : real) := imp (real_le (real_add x1 (real_sub x0 x1)) (real_add x1 x2)).
Definition term274 (x0 : real) (x1 : real) (x2 : real) := imp (real_le (real_add x1 (real_add (real_sub x0 x1) x1)) (real_add x1 x2)).
Definition term150 (x0 : real) := real_le (real_add (real_neg x0) x0).
Definition term285 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_le (real_add (real_add (real_sub x1 x2) x2) x2) (real_add x0 x2)) -> (real_le (real_add (real_sub x1 x2) x2) (real_add x3 x2)) -> real_le x1 (real_add x2 x3).
Definition term4 (x0 : real) (x1 : real) := (fun y0 : real => (real_add x0 y0) = (real_add y0 x0)) x1.
Definition term129 (x0 : real) := real_le x0 (real_of_num (NUMERAL 0)).
Definition term314 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real) := (x0 (real_add x1 x3)) -> real_le x1 (real_sub x2 x3).
Definition term158 (x0 : real) := real_add (real_of_num (NUMERAL 0)) (real_neg x0).
Definition term224 (x0 : real) (x1 : real) (x2 : real) := real_le (real_add (real_neg x1) (real_add x0 x1)) (real_add (real_neg x1) x2).
Definition term96 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term301 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real) := (fun y0 : real => (forall y1 : real, (x0 (real_add y1 x1)) -> real_le y1 y0) -> real_le x2 y0) x3.
Definition term160 (x0 : real) := imp (real_le (real_of_num (NUMERAL 0)) (real_add (real_of_num (NUMERAL 0)) (real_neg x0))).
Definition term162 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (real_neg x0).
Definition term106 (x0 : Prop) := (fun y0 : Prop => y0 -> (~ y0) -> x0) False.
Definition term140 := forall y0 : real, True.
Definition term178 (x0 : real -> Prop) (x1 : real) (x2 : real) := imp (x0 (real_add x1 x2)).
Definition term142 (x0 : Prop) := forall y0 : real, x0.
Definition term34 (x0 : real) := real_add x0 (real_of_num (NUMERAL 0)).
Definition term253 (x0 : real) (x1 : real) (x2 : real) := real_le x0 (real_add x1 x2).
Definition term235 (x0 : real) (x1 : real) (x2 : real) := imp (real_le (real_add x0 (real_add x2 (real_neg x2))) (real_add x1 (real_neg x2))).
Definition term227 (x0 : real) (x1 : real) := real_le (real_add (real_neg x1) (real_add x0 x1)).
Definition term124 := (fun y0 : real => forall y1 : real, (real_le y0 y1) \/ (real_le y1 y0)) (real_of_num (NUMERAL 0)).
Definition term125 := forall y0 : real, (real_le (real_of_num (NUMERAL 0)) y0) \/ (real_le y0 (real_of_num (NUMERAL 0))).
Definition term110 (x0 : Prop) := (~ False) -> x0.
Definition term153 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (real_add (real_neg x0) (real_of_num (NUMERAL 0))).
Definition term56 := forall y0 : real, forall y1 : real, (real_le y0 y1) -> forall y2 : real, real_le (real_add y2 y0) (real_add y2 y1).
Definition term47 (x0 : real) := forall y0 : real, forall y1 : real, (real_le y0 y1) -> real_le (real_add x0 y0) (real_add x0 y1).
Definition term45 := forall y0 : real, forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2).
Definition term18 := forall y0 : real, forall y1 : real, forall y2 : real, (real_add (real_add y0 y1) y2) = (real_add y0 (real_add y1 y2)).
Definition term17 := forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2).
Definition term14 (x0 : real) := forall y0 : real, forall y1 : real, (real_add (real_add x0 y0) y1) = (real_add x0 (real_add y0 y1)).
Definition term13 (x0 : real) := forall y0 : real, forall y1 : real, (real_add x0 (real_add y0 y1)) = (real_add (real_add x0 y0) y1).
Definition term166 (x0 : real -> Prop) (x1 : real) (x2 : real) := x0 (real_add x1 x2).
Definition term32 (x0 : real) (x1 : real) := real_add (real_add x0 (real_neg x1)) x1.
Definition term232 (x0 : real) (x1 : real) := real_le (real_add x0 (real_add x1 (real_neg x1))).
Definition term295 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_le (real_add x1 (real_add (real_neg x2) (real_add x2 x2))) (real_add x0 x2)) -> (real_le (real_add x1 (real_of_num (NUMERAL 0))) (real_add x3 x2)) -> real_le x1 (real_add x2 x3).
Definition term151 := real_le (real_of_num (NUMERAL 0)).
Definition term67 (x0 : real) := (fun y0 : real => (real_add y0 (real_neg y0)) = (real_of_num (NUMERAL 0))) x0.
Definition term298 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_le (real_add x1 (real_add (real_neg x2) (real_add x2 x2))) (real_add x0 x2)) -> (real_le x1 (real_add x3 x2)) -> real_le x1 (real_add x2 x3).
Definition term321 (x0 : real) (x1 : real) := @eq real (real_add x1 (real_sub x0 x1)).
Definition term78 (x0 : Prop) (x1 : Prop) := (False -> x1) -> x0 -> (x0 -> False) -> x1.
Definition term312 (x0 : real) (x1 : real) := @eq real (real_add x0 (real_add x1 (real_neg x1))).
Definition term10 (x0 : real) (x1 : real) := forall y0 : real, (real_add (real_add x0 x1) y0) = (real_add x0 (real_add x1 y0)).
Definition term73 (x0 : Prop) (x1 : Prop) := (True -> x1) -> x0 -> (x0 -> True) -> x1.
Definition term99 (x0 : Prop) (x1 : Prop) := True -> x0 -> (~ x0) -> x1.
Definition term307 (x0 : real) (x1 : real) (x2 : real) := imp (real_le (real_add (real_neg x1) (real_add x0 x1)) (real_add (real_neg x1) x2)).
Definition term246 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_add x0 x2) x1) -> real_le x0 (real_add x1 (real_neg x2)).
Definition term252 (x0 : real -> Prop) (x1 : real) (x2 : real) := imp (x0 (real_add (real_sub x1 x2) x2)).
Definition term75 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x1 -> x2) -> x0 -> (x0 -> x1) -> x2.
Definition term334 (x0 : real -> Prop) := fun y0 : real => x0 y0.
Definition term249 (x0 : real) (x1 : real -> Prop) := ((exists y0 : real, (forall y1 : real, (x1 (real_add y1 x0)) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x1 (real_add y2 x0)) -> real_le y2 y1) -> real_le y0 y1)) -> exists y0 : real, (forall y1 : real, (x1 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x1 y2) -> real_le y2 y1) -> real_le y0 y1)) -> ((exists y0 : real, (x1 (real_add y0 x0)) /\ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (exists y0 : real, forall y1 : real, (x1 (real_add y1 x0)) -> real_le y1 y0)) -> (((exists y0 : real, (x1 (real_add y0 x0)) /\ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (exists y0 : real, forall y1 : real, (x1 (real_add y1 x0)) -> real_le y1 y0)) -> exists y0 : real, (forall y1 : real, (x1 (real_add y1 x0)) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x1 (real_add y2 x0)) -> real_le y2 y1) -> real_le y0 y1)) -> exists y0 : real, (forall y1 : real, (x1 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x1 y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term265 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_sub x0 x1) x2) -> forall y0 : real, real_le (real_add y0 (real_sub x0 x1)) (real_add y0 x2).
Definition term258 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_add (real_sub x0 x1) x1) x2) -> forall y0 : real, real_le (real_add y0 (real_add (real_sub x0 x1) x1)) (real_add y0 x2).
Definition term221 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_add x0 x1) x2) -> forall y0 : real, real_le (real_add y0 (real_add x0 x1)) (real_add y0 x2).
Definition term0 (x0 : real) := (fun y0 : real => (real_add (real_of_num (NUMERAL 0)) y0) = y0) x0.
Definition term132 (x0 : real -> Prop) := exists y0 : real, x0 y0.
Definition term145 (x0 : real -> Prop) := fun y0 : real => (x0 y0) /\ (real_le (real_of_num (NUMERAL 0)) y0).
Definition term44 (x0 : Prop) (x1 : Prop) := ((x0 = x1) -> x0 -> x1) -> (x0 = x1) -> x0 -> x1.
Definition term268 (x0 : real) (x1 : real) (x2 : real) := real_le (real_add x1 (real_sub x0 x1)) (real_add x1 x2).
Definition term239 (x0 : real) := real_le (real_add x0 (real_of_num (NUMERAL 0))).
Definition term12 (x0 : real) := fun y0 : real => forall y1 : real, (real_add (real_add x0 y0) y1) = (real_add x0 (real_add y0 y1)).
Definition term77 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 -> x1) -> x0 -> (x0 -> y0) -> x1) False.
Definition term100 (x0 : Prop) := fun y0 : Prop => y0 -> (~ y0) -> x0.
Definition term7 (x0 : real) (x1 : real) := fun y0 : real => (real_add x0 (real_add x1 y0)) = (real_add (real_add x0 x1) y0).
Definition term170 (x0 : real -> Prop) (x1 : real) (x2 : real) := (x0 (real_add x2 x1)) /\ (real_le (real_of_num (NUMERAL 0)) x2).
Definition term262 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real) := (fun y0 : real => (x0 (real_add y0 x1)) -> real_le y0 x2) x3.
Definition term92 (x0 : Prop) := imp (False -> x0).
Definition term190 (x0 : real -> Prop) (x1 : real) := (exists y0 : real, (x0 (real_add y0 x1)) /\ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (exists y0 : real, forall y1 : real, (x0 (real_add y1 x1)) -> real_le y1 y0).
Definition term189 (x0 : real -> Prop) (x1 : real) := (exists y0 : real, ((fun y1 : real => x0 (real_add y1 x1)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (exists y0 : real, forall y1 : real, ((fun y2 : real => x0 (real_add y2 x1)) y1) -> real_le y1 y0).
Definition term120 (x0 : real -> Prop) := (exists y0 : real, (x0 y0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (exists y0 : real, forall y1 : real, (x0 y1) -> real_le y1 y0).
Definition term30 (x0 : real) (x1 : real) := real_add (real_add x0 (real_neg x1)).
Definition term248 (x0 : real -> Prop) (x1 : real) (x2 : real) := forall y0 : real, (x0 (real_add y0 x2)) -> real_le y0 (real_add x1 (real_neg x2)).
Definition term20 (x0 : real) := real_add (real_neg x0) x0.
Definition term202 (x0 : real -> Prop) (x1 : real) (x2 : real) := forall y0 : real, (forall y1 : real, (x0 (real_add y1 x1)) -> real_le y1 y0) -> real_le x2 y0.
Definition term201 (x0 : real -> Prop) (x1 : real) (x2 : real) := forall y0 : real, (forall y1 : real, ((fun y2 : real => x0 (real_add y2 x1)) y1) -> real_le y1 y0) -> real_le x2 y0.
Definition term102 (x0 : Prop) := (fun y0 : Prop => y0 -> (~ y0) -> x0) True.
Definition term9 (x0 : real) (x1 : real) := forall y0 : real, (real_add x0 (real_add x1 y0)) = (real_add (real_add x0 x1) y0).
Definition term130 (x0 : real -> Prop) := (exists y0 : real, x0 y0) /\ (exists y0 : real, forall y1 : real, (x0 y1) -> real_le y1 y0).
Definition term328 (x0 : real -> Prop) (x1 : real) (x2 : real) := forall y0 : real, (forall y1 : real, (x0 y1) -> real_le y1 y0) -> real_le (real_add x1 x2) y0.
Definition term324 (x0 : real) (x1 : real) := real_le (real_add x0 x1).
Definition term304 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real) := (forall y0 : real, (x0 (real_add y0 x3)) -> real_le y0 (real_sub x2 x3)) -> real_le x1 (real_sub x2 x3).
Definition term177 (x0 : real -> Prop) (x1 : real) (x2 : real) := imp ((fun y0 : real => x0 (real_add y0 x1)) x2).
Definition term76 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop ((x1 -> x2) -> x0 -> (x0 -> x1) -> x2).
Definition term294 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_add x0 (real_of_num (NUMERAL 0))) (real_add x2 x1)) -> real_le x0 (real_add x1 x2).
Definition term282 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_add x2 (real_sub x0 x2)) (real_add x2 x1)) -> real_le x0 (real_add x1 x2).
Definition term279 (x0 : real) (x1 : real) (x2 : real) := real_le (real_add (real_sub x0 x2) x2) (real_add x1 x2).
Definition term273 (x0 : real) (x1 : real) (x2 : real) := real_le (real_add (real_add (real_sub x0 x2) x2) x2) (real_add x1 x2).
Definition term335 (x0 : real -> Prop) := ((exists y0 : real, x0 y0) /\ (exists y0 : real, forall y1 : real, (x0 y1) -> real_le y1 y0)) -> exists y0 : real, (forall y1 : real, (x0 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x0 y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term209 (x0 : real -> Prop) (x1 : real) := ((exists y0 : real, (x0 (real_add y0 x1)) /\ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (exists y0 : real, forall y1 : real, (x0 (real_add y1 x1)) -> real_le y1 y0)) -> exists y0 : real, (forall y1 : real, (x0 (real_add y1 x1)) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x0 (real_add y2 x1)) -> real_le y2 y1) -> real_le y0 y1).
Definition term119 (x0 : real -> Prop) := ((exists y0 : real, (x0 y0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (exists y0 : real, forall y1 : real, (x0 y1) -> real_le y1 y0)) -> exists y0 : real, (forall y1 : real, (x0 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x0 y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term116 (x0 : real -> Prop) (x1 : real) := ((exists y0 : real, ((fun y1 : real => x0 (real_add y1 x1)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (exists y0 : real, forall y1 : real, ((fun y2 : real => x0 (real_add y2 x1)) y1) -> real_le y1 y0)) -> exists y0 : real, (forall y1 : real, ((fun y2 : real => x0 (real_add y2 x1)) y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, ((fun y3 : real => x0 (real_add y3 x1)) y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term329 (x0 : real -> Prop) (x1 : real) (x2 : real) := (forall y0 : real, (x0 y0) -> real_le y0 (real_add x1 x2)) /\ (forall y0 : real, (forall y1 : real, (x0 y1) -> real_le y1 y0) -> real_le (real_add x1 x2) y0).
Definition term204 (x0 : real -> Prop) (x1 : real) (x2 : real) := (forall y0 : real, (x0 (real_add y0 x1)) -> real_le y0 x2) /\ (forall y0 : real, (forall y1 : real, (x0 (real_add y1 x1)) -> real_le y1 y0) -> real_le x2 y0).
Definition term203 (x0 : real -> Prop) (x1 : real) (x2 : real) := (forall y0 : real, ((fun y1 : real => x0 (real_add y1 x1)) y0) -> real_le y0 x2) /\ (forall y0 : real, (forall y1 : real, ((fun y2 : real => x0 (real_add y2 x1)) y1) -> real_le y1 y0) -> real_le x2 y0).
Definition term192 (x0 : real -> Prop) (x1 : real) := imp ((exists y0 : real, (x0 (real_add y0 x1)) /\ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (exists y0 : real, forall y1 : real, (x0 (real_add y1 x1)) -> real_le y1 y0)).
Definition term191 (x0 : real -> Prop) (x1 : real) := imp ((exists y0 : real, ((fun y1 : real => x0 (real_add y1 x1)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (exists y0 : real, forall y1 : real, ((fun y2 : real => x0 (real_add y2 x1)) y1) -> real_le y1 y0)).
Definition term42 (x0 : Prop) (x1 : Prop) := (x0 = x1) -> x0 -> x1.
Definition term81 (x0 : Prop) (x1 : Prop) := (x0 -> True) -> x1.
Definition term296 (x0 : real) (x1 : real) (x2 : real) := imp (real_le x0 (real_add x1 x2)).
Definition term240 (x0 : real) (x1 : real) (x2 : real) := real_le (real_add x0 (real_of_num (NUMERAL 0))) (real_add x1 (real_neg x2)).
Definition term288 (x0 : real) (x1 : real) := real_add x0 (real_add (real_neg x1) (real_add x1 x1)).
Definition term323 (x0 : real) (x1 : real) := @eq real (real_add (real_add x0 (real_neg x1)) x1).
Definition term31 (x0 : real) (x1 : real) := real_add (real_sub x0 x1) x1.
Definition term39 := forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0.
Definition term271 (x0 : real) (x1 : real) := real_le (real_add x1 (real_add (real_sub x0 x1) x1)).
Definition term53 (x0 : real) (x1 : real) := forall y0 : real, real_le (real_add y0 x0) (real_add y0 x1).
Definition term63 := fun y0 : real => (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0)).
Definition term287 (x0 : real) (x1 : real) := real_add (real_add x0 (real_neg x1)) (real_add x1 x1).
Definition term186 (x0 : real -> Prop) (x1 : real) := fun y0 : real => forall y1 : real, (x0 (real_add y1 x1)) -> real_le y1 y0.
Definition term185 (x0 : real -> Prop) (x1 : real) := fun y0 : real => forall y1 : real, ((fun y2 : real => x0 (real_add y2 x1)) y1) -> real_le y1 y0.
Definition term143 (x0 : real -> Prop) := fun y0 : real => forall y1 : real, (x0 y1) -> real_le y1 y0.
Definition term11 (x0 : real) := fun y0 : real => forall y1 : real, (real_add x0 (real_add y0 y1)) = (real_add (real_add x0 y0) y1).
Definition term24 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_add (real_add x0 x1) y0) = (real_add x0 (real_add x1 y0))) x2.
Definition term319 (x0 : real) (x1 : real) (x2 : real) := real_le (real_add x2 x0) (real_add x2 (real_sub x1 x2)).
Definition term332 (x0 : real) (x1 : real -> Prop) := ((exists y0 : real, (x1 (real_add y0 x0)) /\ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (exists y0 : real, forall y1 : real, (x1 (real_add y1 x0)) -> real_le y1 y0)) -> (((exists y0 : real, (x1 (real_add y0 x0)) /\ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (exists y0 : real, forall y1 : real, (x1 (real_add y1 x0)) -> real_le y1 y0)) -> exists y0 : real, (forall y1 : real, (x1 (real_add y1 x0)) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x1 (real_add y2 x0)) -> real_le y2 y1) -> real_le y0 y1)) -> exists y0 : real, (forall y1 : real, (x1 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x1 y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term325 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_add x1 x0) (real_add x1 (real_sub x2 x1))) -> real_le (real_add x0 x1) x2.
Definition term58 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) -> forall y2 : real, real_le (real_add y2 y0) (real_add y2 y1)) x0.
Definition term25 (x0 : real) := (fun y0 : real => forall y1 : real, (real_sub y0 y1) = (real_add y0 (real_neg y1))) x0.
Definition term2 (x0 : real) := (fun y0 : real => forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) x0.
Definition term305 (x0 : real -> Prop) (x1 : real) (x2 : real) := (forall y0 : real, (x0 y0) -> real_le y0 x2) -> real_le x1 x2.
Definition term331 (x0 : real) (x1 : real -> Prop) := (exists y0 : real, (forall y1 : real, (x1 (real_add y1 x0)) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x1 (real_add y2 x0)) -> real_le y2 y1) -> real_le y0 y1)) -> exists y0 : real, (forall y1 : real, (x1 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x1 y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term154 (x0 : real) := imp (real_le (real_add (real_neg x0) x0) (real_add (real_neg x0) (real_of_num (NUMERAL 0)))).
Definition term64 := fun y0 : real => (real_add y0 (real_neg y0)) = (real_of_num (NUMERAL 0)).
Definition term105 (x0 : Prop) (x1 : Prop) := @eq Prop (x0 -> (~ x0) -> x1).
Definition term85 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => y0 -> x0 -> y0) x1.
Definition term104 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => y0 -> (~ y0) -> x0) x1).
Definition term88 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => y0 -> x0 -> y0) x1).
Definition term247 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real) := (x0 (real_add x1 x3)) -> real_le x1 (real_add x2 (real_neg x3)).
Definition term208 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (forall y1 : real, (x0 (real_add y1 x1)) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x0 (real_add y2 x1)) -> real_le y2 y1) -> real_le y0 y1).
Definition term207 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (forall y1 : real, ((fun y2 : real => x0 (real_add y2 x1)) y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, ((fun y3 : real => x0 (real_add y3 x1)) y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term121 (x0 : real -> Prop) := exists y0 : real, (forall y1 : real, (x0 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x0 y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term128 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term242 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_add x0 (real_of_num (NUMERAL 0))) (real_add x1 (real_neg x2))) -> real_le x0 (real_add x1 (real_neg x2)).
Definition term238 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_add x0 (real_add x2 (real_neg x2))) (real_add x1 (real_neg x2))) -> real_le x0 (real_add x1 (real_neg x2)).
Definition term237 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_add (real_add x0 x2) (real_neg x2)) (real_add x1 (real_neg x2))) -> real_le x0 (real_add x1 (real_neg x2)).
Definition term172 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (x0 (real_add y0 x1)) /\ (real_le (real_of_num (NUMERAL 0)) y0).
Definition term306 (x0 : real -> Prop) (x1 : real) := (forall y0 : real, (x0 y0) -> real_le y0 x1) -> forall y0 : real, (x0 y0) -> real_le y0 x1.
Definition term303 (x0 : real -> Prop) (x1 : real) (x2 : real) := (forall y0 : real, (forall y1 : real, (x0 (real_add y1 x1)) -> real_le y1 y0) -> real_le x2 y0) -> forall y0 : real, (forall y1 : real, (x0 (real_add y1 x1)) -> real_le y1 y0) -> real_le x2 y0.
Definition term138 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (x0 y0) -> real_le y0 x1.
Definition term218 (x0 : real -> Prop) (x1 : real) := (x0 (real_add (real_of_num (NUMERAL 0)) x1)) /\ (real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term33 (x0 : real) (x1 : real) := real_add x0 (real_add (real_neg x1) x1).
Definition term19 (x0 : real) := (fun y0 : real => (real_add (real_neg y0) y0) = (real_of_num (NUMERAL 0))) x0.
Definition term144 (x0 : real -> Prop) := exists y0 : real, (x0 y0) /\ (real_le (real_of_num (NUMERAL 0)) y0).
Definition term136 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (x0 y0) -> real_le y0 x1) x2.
Definition term62 (x0 : real) := @eq real (real_add x0 (real_neg x0)).
Definition term52 (x0 : real) (x1 : real) (x2 : real) := real_le (real_add x1 x0) (real_add x1 x2).
Definition term69 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term163 (x0 : real) := imp (real_le (real_of_num (NUMERAL 0)) (real_neg x0)).
Definition term26 (x0 : real) := forall y0 : real, (real_sub x0 y0) = (real_add x0 (real_neg y0)).
Definition term60 (x0 : real) := real_add x0 (real_neg x0).
Definition term308 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_add (real_neg x2) (real_add x0 x2)) (real_add (real_neg x2) x1)) -> real_le x0 (real_sub x1 x2).
Definition term79 (x0 : Prop) := imp (True -> x0).
Definition term283 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_add (real_sub x0 x1) x1) (real_add x2 x1)) -> real_le x0 (real_add x1 x2).
Definition term48 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) -> real_le (real_add x0 y0) (real_add x0 y1)) x1.
Definition term23 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_add (real_add x0 y0) y1) = (real_add x0 (real_add y0 y1))) x1.
Definition term263 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real) := (x0 (real_add (real_sub x1 x2) x2)) -> real_le (real_sub x1 x2) x3.
Definition term256 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real) := (x0 (real_add (real_sub x1 x2) x2)) -> real_le (real_add (real_sub x1 x2) x2) x3.
Definition term80 (x0 : Prop) := imp (x0 -> True).
Definition term86 (x0 : Prop) := (fun y0 : Prop => y0 -> x0 -> y0) True.
Definition term213 (x0 : real) (x1 : real -> Prop) := (((exists y0 : real, (x1 (real_add y0 x0)) /\ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (exists y0 : real, forall y1 : real, (x1 (real_add y1 x0)) -> real_le y1 y0)) -> exists y0 : real, (forall y1 : real, (x1 (real_add y1 x0)) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x1 (real_add y2 x0)) -> real_le y2 y1) -> real_le y0 y1)) -> exists y0 : real, (forall y1 : real, (x1 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x1 y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term212 (x0 : real) (x1 : real -> Prop) := (((exists y0 : real, ((fun y1 : real => x1 (real_add y1 x0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (exists y0 : real, forall y1 : real, ((fun y2 : real => x1 (real_add y2 x0)) y1) -> real_le y1 y0)) -> exists y0 : real, (forall y1 : real, ((fun y2 : real => x1 (real_add y2 x0)) y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, ((fun y3 : real => x1 (real_add y3 x0)) y2) -> real_le y2 y1) -> real_le y0 y1)) -> exists y0 : real, (forall y1 : real, (x1 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x1 y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term264 (x0 : real) (x1 : real) (x2 : real) := real_le (real_sub x0 x1) x2.
Definition term112 (x0 : Prop) (x1 : Prop) (x2 : Prop) := ((x1 -> x2) -> x0 -> (x0 -> x1) -> x2) -> x0 -> (x0 -> x1) -> x2.
Definition term336 := forall y0 : real -> Prop, ((exists y1 : real, y0 y1) /\ (exists y1 : real, forall y2 : real, (y0 y2) -> real_le y2 y1)) -> exists y1 : real, (forall y2 : real, (y0 y2) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (y0 y3) -> real_le y3 y2) -> real_le y1 y2).
Definition term117 := forall y0 : real -> Prop, ((exists y1 : real, (y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y1)) /\ (exists y1 : real, forall y2 : real, (y0 y2) -> real_le y2 y1)) -> exists y1 : real, (forall y2 : real, (y0 y2) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (y0 y3) -> real_le y3 y2) -> real_le y1 y2).
Definition term266 (x0 : real) (x1 : real) (x2 : real) := forall y0 : real, real_le (real_add y0 (real_sub x0 x1)) (real_add y0 x2).
Definition term259 (x0 : real) (x1 : real) (x2 : real) := forall y0 : real, real_le (real_add y0 (real_add (real_sub x0 x1) x1)) (real_add y0 x2).
Definition term222 (x0 : real) (x1 : real) (x2 : real) := forall y0 : real, real_le (real_add y0 (real_add x0 x1)) (real_add y0 x2).
Definition term49 (x0 : real) (x1 : real) := forall y0 : real, (real_le x0 y0) -> real_le (real_add x1 x0) (real_add x1 y0).
Definition term233 (x0 : real) (x1 : real) (x2 : real) := real_le (real_add x0 (real_add x2 (real_neg x2))) (real_add x1 (real_neg x2)).
Definition term27 (x0 : real) (x1 : real) := (fun y0 : real => (real_sub x0 y0) = (real_add x0 (real_neg y0))) x1.
Definition term5 (x0 : real) (x1 : real) (x2 : real) := real_add x0 (real_add x1 x2).
Definition term159 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (real_add (real_of_num (NUMERAL 0)) (real_neg x0)).
Definition term35 (x0 : real) := @eq real (real_add (real_of_num (NUMERAL 0)) x0).
Definition term127 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) \/ (real_le x0 (real_of_num (NUMERAL 0))).
Definition term223 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => real_le (real_add y0 (real_add x0 x2)) (real_add y0 x1)) (real_neg x2).
Definition term16 := fun y0 : real => forall y1 : real, forall y2 : real, (real_add (real_add y0 y1) y2) = (real_add y0 (real_add y1 y2)).
Definition term15 := fun y0 : real => forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2).
Definition term211 (x0 : real -> Prop) (x1 : real) := imp (((exists y0 : real, (x0 (real_add y0 x1)) /\ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (exists y0 : real, forall y1 : real, (x0 (real_add y1 x1)) -> real_le y1 y0)) -> exists y0 : real, (forall y1 : real, (x0 (real_add y1 x1)) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x0 (real_add y2 x1)) -> real_le y2 y1) -> real_le y0 y1)).
Definition term210 (x0 : real -> Prop) (x1 : real) := imp (((exists y0 : real, ((fun y1 : real => x0 (real_add y1 x1)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) /\ (exists y0 : real, forall y1 : real, ((fun y2 : real => x0 (real_add y2 x1)) y1) -> real_le y1 y0)) -> exists y0 : real, (forall y1 : real, ((fun y2 : real => x0 (real_add y2 x1)) y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, ((fun y3 : real => x0 (real_add y3 x1)) y2) -> real_le y2 y1) -> real_le y0 y1)).
Definition term214 (x0 : real) := (fun y0 : real => real_le y0 y0) x0.
Definition term29 (x0 : real) (x1 : real) := real_add (real_sub x0 x1).
Definition term101 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => y0 -> (~ y0) -> x0) x1.
Definition term286 (x0 : real) (x1 : real) := real_add (real_sub x0 x1) (real_add x1 x1).
Definition term270 (x0 : real) (x1 : real) := real_add (real_add (real_sub x0 x1) x1) x1.
Definition term111 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> (x0 -> x1) -> x2.
Definition term318 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => real_le (real_add y0 x0) (real_add y0 (real_sub x1 x2))) x2.
Definition term83 (x0 : Prop) (x1 : Prop) := x1 -> x0 -> x1.
Definition term40 := forall y0 : real, (real_add y0 (real_of_num (NUMERAL 0))) = y0.
Definition term50 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_le x0 y0) -> real_le (real_add x1 x0) (real_add x1 y0)) x2.
Definition term169 (x0 : real -> Prop) (x1 : real) (x2 : real) := ((fun y0 : real => x0 (real_add y0 x1)) x2) /\ (real_le (real_of_num (NUMERAL 0)) x2).
Definition term254 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real) := (x0 x1) -> real_le x1 (real_add x2 x3).
Definition term245 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_add (real_neg x2) (real_add x0 x2)) (real_add (real_neg x2) x1)) -> real_le x0 (real_add x1 (real_neg x2)).
Definition term267 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => real_le (real_add y0 (real_sub x0 x2)) (real_add y0 x1)) x2.
Definition term260 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => real_le (real_add y0 (real_add (real_sub x0 x2) x2)) (real_add y0 x1)) x2.
Definition term174 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (x0 (real_add y0 x1)) /\ (real_le (real_of_num (NUMERAL 0)) y0).
Definition term8 (x0 : real) (x1 : real) := fun y0 : real => (real_add (real_add x0 x1) y0) = (real_add x0 (real_add x1 y0)).
Definition term93 (x0 : Prop) := imp (x0 -> False).
Definition term1 (x0 : real) := real_add (real_of_num (NUMERAL 0)) x0.
Definition term183 (x0 : real -> Prop) (x1 : real) (x2 : real) := forall y0 : real, ((fun y1 : real => x0 (real_add y1 x1)) y0) -> real_le y0 x2.
Definition term55 (x0 : real) := forall y0 : real, (real_le x0 y0) -> forall y1 : real, real_le (real_add y1 x0) (real_add y1 y0).
Definition term261 (x0 : real) (x1 : real) (x2 : real) := real_le (real_add x1 (real_add (real_sub x0 x1) x1)) (real_add x1 x2).
Definition term95 (x0 : Prop) (x1 : Prop) := (x0 -> False) -> x1.
Definition term226 (x0 : real) (x1 : real) := real_add (real_add x0 x1) (real_neg x1).
Definition term155 (x0 : real) := imp (real_le (real_of_num (NUMERAL 0)) (real_add (real_neg x0) (real_of_num (NUMERAL 0)))).
Definition term297 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 (real_add x2 x1)) -> real_le x0 (real_add x1 x2).
Definition term313 (x0 : real) (x1 : real) (x2 : real) := (real_le (real_add x0 x2) x1) -> real_le x0 (real_sub x1 x2).
Definition term234 (x0 : real) (x1 : real) (x2 : real) := imp (real_le (real_add (real_add x0 x2) (real_neg x2)) (real_add x1 (real_neg x2))).
Definition term103 (x0 : Prop) := True -> (~ True) -> x0.
Definition term196 (x0 : real -> Prop) (x1 : real) (x2 : real) := imp (forall y0 : real, (x0 (real_add y0 x1)) -> real_le y0 x2).
Definition term195 (x0 : real -> Prop) (x1 : real) (x2 : real) := imp (forall y0 : real, ((fun y1 : real => x0 (real_add y1 x1)) y0) -> real_le y0 x2).
Definition term228 (x0 : real) (x1 : real) := real_le (real_add (real_add x0 x1) (real_neg x1)).
Definition term66 := forall y0 : real, (real_add y0 (real_neg y0)) = (real_of_num (NUMERAL 0)).
Definition term156 (x0 : real) (x1 : real -> Prop) := (real_le (real_add (real_neg x0) x0) (real_add (real_neg x0) (real_of_num (NUMERAL 0)))) -> exists y0 : real, (forall y1 : real, (x1 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x1 y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term146 (x0 : real) := (real_le x0 (real_of_num (NUMERAL 0))) -> forall y0 : real, real_le (real_add y0 x0) (real_add y0 (real_of_num (NUMERAL 0))).
Definition term291 (x0 : real) (x1 : real) (x2 : real) := imp (real_le (real_add x0 (real_add (real_neg x2) (real_add x2 x2))) (real_add x1 x2)).
Definition term168 (x0 : real -> Prop) (x1 : real) (x2 : real) := and (x0 (real_add x1 x2)).
Definition term161 (x0 : real) (x1 : real -> Prop) := (real_le (real_of_num (NUMERAL 0)) (real_add (real_of_num (NUMERAL 0)) (real_neg x0))) -> exists y0 : real, (forall y1 : real, (x1 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x1 y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term182 (x0 : real -> Prop) (x1 : real) (x2 : real) := fun y0 : real => (x0 (real_add y0 x1)) -> real_le y0 x2.
Definition term284 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_le (real_add x3 (real_add (real_sub x1 x3) x3)) (real_add x3 x0)) -> (real_le (real_add x3 (real_sub x1 x3)) (real_add x3 x2)) -> real_le x1 (real_add x2 x3).
Definition term257 (x0 : real) (x1 : real) (x2 : real) := real_le (real_add (real_sub x0 x1) x1) x2.
Definition term326 (x0 : real) (x1 : real) (x2 : real) := (real_le x0 (real_sub x2 x1)) -> real_le (real_add x0 x1) x2.
Definition term133 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (x0 y0) -> real_le y0 x1.
Definition term108 (x0 : Prop) := (~ True) -> x0.
Definition term43 (x0 : Prop) (x1 : Prop) := ((x0 = x1) -> x0 -> x1) -> x0 -> x1.
Definition term109 := imp (~ True).
Definition term230 (x0 : real) (x1 : real) (x2 : real) := real_le (real_add (real_add x0 x2) (real_neg x2)) (real_add x1 (real_neg x2)).
Definition term147 (x0 : real) := forall y0 : real, real_le (real_add y0 x0) (real_add y0 (real_of_num (NUMERAL 0))).
Definition term123 := (forall y0 : real -> Prop, ((exists y1 : real, (y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y1)) /\ (exists y1 : real, forall y2 : real, (y0 y2) -> real_le y2 y1)) -> exists y1 : real, (forall y2 : real, (y0 y2) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (y0 y3) -> real_le y3 y2) -> real_le y1 y2)) -> forall y0 : real -> Prop, ((exists y1 : real, (y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y1)) /\ (exists y1 : real, forall y2 : real, (y0 y2) -> real_le y2 y1)) -> exists y1 : real, (forall y2 : real, (y0 y2) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (y0 y3) -> real_le y3 y2) -> real_le y1 y2).
Definition term320 (x0 : real) (x1 : real) (x2 : real) := ((real_le (real_add x1 x0) (real_add x1 (real_sub x2 x1))) = (real_le (real_add x0 x1) x2)) -> (real_le (real_add x1 x0) (real_add x1 (real_sub x2 x1))) -> real_le (real_add x0 x1) x2.
Definition term276 (x0 : real) (x1 : real) := real_add x1 (real_sub x0 x1).
Definition term277 (x0 : real) (x1 : real) := real_le (real_add x1 (real_sub x0 x1)).
Definition term231 (x0 : real) (x1 : real) := real_add x0 (real_add x1 (real_neg x1)).
Definition term148 (x0 : real) := (fun y0 : real => real_le (real_add y0 x0) (real_add y0 (real_of_num (NUMERAL 0)))) (real_neg x0).
Definition term251 (x0 : real -> Prop) (x1 : real) := imp (x0 x1).
Definition term299 (x0 : real -> Prop) (x1 : real) (x2 : real) := forall y0 : real, (x0 y0) -> real_le y0 (real_add x1 x2).
Definition term41 (x0 : real) := (fun y0 : real => (real_add y0 (real_of_num (NUMERAL 0))) = y0) x0.
Definition term6 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add x0 x1) x2.
Definition term300 (x0 : real) (x1 : real) (x2 : real) := real_le x0 (real_sub x1 x2).
Definition term68 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term315 (x0 : real -> Prop) (x1 : real) (x2 : real) := forall y0 : real, (x0 (real_add y0 x2)) -> real_le y0 (real_sub x1 x2).
Definition term236 (x0 : real) (x1 : real) (x2 : real) := real_le x0 (real_add x1 (real_neg x2)).
Definition term70 (x0 : Prop) (x1 : Prop) := fun y0 : Prop => (y0 -> x1) -> x0 -> (x0 -> y0) -> x1.
Definition term322 (x0 : real) (x1 : real) := @eq real (real_add (real_sub x0 x1) x1).
Definition term215 (x0 : real -> Prop) (x1 : real) := x0 (real_add (real_of_num (NUMERAL 0)) x1).
Definition term46 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_le y1 y2) -> real_le (real_add y0 y1) (real_add y0 y2)) x0.
Definition term22 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_add (real_add y0 y1) y2) = (real_add y0 (real_add y1 y2))) x0.
Definition term176 (x0 : real -> Prop) (x1 : real) := and (exists y0 : real, (x0 (real_add y0 x1)) /\ (real_le (real_of_num (NUMERAL 0)) y0)).
Definition term175 (x0 : real -> Prop) (x1 : real) := and (exists y0 : real, ((fun y1 : real => x0 (real_add y1 x1)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y0)).
Definition term200 (x0 : real -> Prop) (x1 : real) (x2 : real) := fun y0 : real => (forall y1 : real, (x0 (real_add y1 x1)) -> real_le y1 y0) -> real_le x2 y0.
Definition term199 (x0 : real -> Prop) (x1 : real) (x2 : real) := fun y0 : real => (forall y1 : real, ((fun y2 : real => x0 (real_add y2 x1)) y1) -> real_le y1 y0) -> real_le x2 y0.
Definition term255 (x0 : real -> Prop) (x1 : real) (x2 : real) (x3 : real) := (x0 (real_add (real_sub x1 x3) x3)) -> real_le x1 (real_add x2 x3).
Definition term115 (x0 : real -> Prop) (x1 : real) := fun y0 : real => x0 (real_add y0 x1).
Definition term126 (x0 : real) := (fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) \/ (real_le y0 (real_of_num (NUMERAL 0)))) x0.
Definition term72 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 -> x1) -> x0 -> (x0 -> y0) -> x1) True.
Definition term118 (x0 : real -> Prop) := (fun y0 : real -> Prop => ((exists y1 : real, (y0 y1) /\ (real_le (real_of_num (NUMERAL 0)) y1)) /\ (exists y1 : real, forall y2 : real, (y0 y2) -> real_le y2 y1)) -> exists y1 : real, (forall y2 : real, (y0 y2) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (y0 y3) -> real_le y3 y2) -> real_le y1 y2)) x0.
Definition term37 := fun y0 : real => (real_add (real_of_num (NUMERAL 0)) y0) = y0.
Definition term87 (x0 : Prop) := True -> x0 -> True.
Definition term278 (x0 : real) (x1 : real) := real_le (real_add (real_sub x0 x1) x1).
Definition term272 (x0 : real) (x1 : real) := real_le (real_add (real_add (real_sub x0 x1) x1) x1).
Definition term225 (x0 : real) (x1 : real) := real_add (real_neg x1) (real_add x0 x1).
Definition term74 (x0 : Prop) (x1 : Prop) (x2 : Prop) := @eq Prop ((fun y0 : Prop => (y0 -> x1) -> x0 -> (x0 -> y0) -> x1) x2).
Definition term90 (x0 : Prop) := (fun y0 : Prop => y0 -> x0 -> y0) False.
Definition term137 (x0 : real -> Prop) (x1 : real) (x2 : real) := (x0 x1) -> real_le x1 x2.
Definition term157 (x0 : real) (x1 : real -> Prop) := (real_le (real_of_num (NUMERAL 0)) (real_add (real_neg x0) (real_of_num (NUMERAL 0)))) -> exists y0 : real, (forall y1 : real, (x1 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x1 y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term250 (x0 : real -> Prop) (x1 : real) (x2 : real) := x0 (real_add (real_sub x1 x2) x2).
