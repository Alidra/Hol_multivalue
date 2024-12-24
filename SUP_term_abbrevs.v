Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term7 (x0 : real -> Prop) := (fun y0 : real -> Prop => (sup y0) = (@ε real (fun y1 : real => (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (@IN real y3 y0) -> real_le y3 y2) -> real_le y1 y2)))) x0.
Definition term291 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (~ (@IN real y0 x0)) \/ (real_le y0 x1)) x2.
Definition term200 (x0 : real -> Prop) := ((exists y0 : real, @IN real y0 x0) \/ (x0 = (@EMPTY real))) /\ ((forall y0 : real, ~ (@IN real y0 x0)) \/ (~ (x0 = (@EMPTY real)))).
Definition term5 (x0 : real -> Prop) := (forall y0 : real -> Prop, ((exists y1 : real, y0 y1) /\ (exists y1 : real, forall y2 : real, (y0 y2) -> real_le y2 y1)) -> exists y1 : real, (forall y2 : real, (y0 y2) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (y0 y3) -> real_le y3 y2) -> real_le y1 y2)) -> exists y0 : real, (forall y1 : real, (x0 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x0 y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term212 (x0 : real -> Prop) := and ((fun y0 : real -> Prop => (exists y1 : real, @IN real y1 y0) \/ (y0 = (@EMPTY real))) x0).
Definition term113 (x0 : real -> Prop) := @eq Prop (exists y0 : real, @IN real y0 x0).
Definition term64 (x0 : real -> Prop) (x1 : real) := fun y0 : real => ((fun y1 : real => @IN real y1 x0) y0) -> real_le y0 x1.
Definition term299 (x0 : type1023) (x1 : real -> Prop) := (~ (@IN real (x0 x1) x1)) -> @IN real (x0 x1) x1.
Definition term129 (x0 : real -> Prop) := ~ (all x0).
Definition term304 := (~ False) -> False.
Definition term80 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le x1 y0.
Definition term79 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (forall y1 : real, ((fun y2 : real => @IN real y2 x0) y1) -> real_le y1 y0) -> real_le x1 y0.
Definition term241 (x0 : real -> Prop) := fun y0 : real => (@IN real y0 x0) \/ (x0 = (@EMPTY real)).
Definition term260 (x0 : type1023) (x1 : real -> Prop) := (@IN real (x0 x1) x1) \/ (x1 = (@EMPTY real)).
Definition term306 (x0 : real -> real) (x1 : real) (x2 : real -> Prop) := (~ (@IN real (x0 x1) x2)) -> @IN real (x0 x1) x2.
Definition term211 (x0 : real -> Prop) := (fun y0 : real -> Prop => (exists y1 : real, @IN real y1 y0) \/ (y0 = (@EMPTY real))) x0.
Definition term45 (x0 : real -> Prop) := @eq Prop ((forall y0 : real, (@IN real y0 x0) -> real_le y0 (@ε real (fun y1 : real => (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (@IN real y3 x0) -> real_le y3 y2) -> real_le y1 y2)))) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le (@ε real (fun y1 : real => (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (@IN real y3 x0) -> real_le y3 y2) -> real_le y1 y2))) y0)).
Definition term293 (x0 : real -> real) (x1 : real) := ~ (real_le (x0 x1) x1).
Definition term116 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (~ (@IN real y0 x0)) \/ (real_le y0 x1).
Definition term312 (x0 : Prop) := ~ (~ x0).
Definition term9 (x0 : real) (x1 : real -> Prop) := real_le x0 (sup x1).
Definition term98 (x0 : real -> Prop) := imp (~ ((exists y0 : real, @IN real y0 x0) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0))).
Definition term187 (x0 : real -> Prop) (x1 : real -> real) := (forall y0 : real, ~ (@IN real y0 x0)) \/ (forall y0 : real, (@IN real (x1 y0) x0) /\ (~ (real_le (x1 y0) y0))).
Definition term268 := and (exists y0 : type1023, forall y1 : real -> Prop, (@IN real (y0 y1) y1) \/ (y1 = (@EMPTY real))).
Definition term191 (x0 : real -> Prop) := ~ (~ (x0 = (@EMPTY real))).
Definition term99 (x0 : real -> Prop) := (~ ((exists y0 : real, @IN real y0 x0) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0))) -> (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> False.
Definition term215 := fun y0 : real -> Prop => ((fun y1 : real -> Prop => (exists y2 : real, @IN real y2 y1) \/ (y1 = (@EMPTY real))) y0) /\ ((fun y1 : real -> Prop => (forall y2 : real, ~ (@IN real y2 y1)) \/ (~ (y1 = (@EMPTY real)))) y0).
Definition term75 (x0 : real -> Prop) (x1 : real) := and (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1).
Definition term74 (x0 : real -> Prop) (x1 : real) := and (forall y0 : real, ((fun y1 : real => @IN real y1 x0) y0) -> real_le y0 x1).
Definition term19 (x0 : real -> Prop) := and (forall y0 : real, (@IN real y0 x0) -> real_le y0 (@ε real (fun y1 : real => (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (@IN real y3 x0) -> real_le y3 y2) -> real_le y1 y2)))).
Definition term18 (x0 : real -> Prop) := and (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)).
Definition term265 := fun y0 : type1023 => forall y1 : real -> Prop, (fun y2 : real -> Prop => fun y3 : real => (@IN real y3 y2) \/ (y2 = (@EMPTY real))) y1 (y0 y1).
Definition term15 (x0 : real -> Prop) := fun y0 : real => (@IN real y0 x0) -> real_le y0 (@ε real (fun y1 : real => (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (@IN real y3 x0) -> real_le y3 y2) -> real_le y1 y2))).
Definition term148 (x0 : real -> Prop) := (forall y0 : real, ~ (@IN real y0 x0)) \/ (forall y0 : real, exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0))).
Definition term286 := fun y0 : type1023 => ((fun y1 : type1023 => forall y2 : real -> Prop, (@IN real (y1 y2) y2) \/ (y2 = (@EMPTY real))) y0) /\ (forall y1 : real -> Prop, (forall y2 : real, ~ (@IN real y2 y1)) \/ (~ (y1 = (@EMPTY real)))).
Definition term69 (x0 : real -> Prop) := exists y0 : real, forall y1 : real, ((fun y2 : real => @IN real y2 x0) y1) -> real_le y1 y0.
Definition term50 (x0 : real -> Prop) := exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0.
Definition term88 (x0 : Prop) := (~ x0) -> False.
Definition term65 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (@IN real y0 x0) -> real_le y0 x1.
Definition term227 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term93 (x0 : real) (x1 : real -> Prop) := ((~ (x1 = (@EMPTY real))) -> (forall y0 : real, (@IN real y0 x1) -> real_le y0 x0) -> (~ ((exists y0 : real, @IN real y0 x1) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x1) -> real_le y1 y0))) -> (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> False) -> (~ (x1 = (@EMPTY real))) -> (forall y0 : real, (@IN real y0 x1) -> real_le y0 x0) -> (~ ((exists y0 : real, @IN real y0 x1) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x1) -> real_le y1 y0))) -> (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> False.
Definition term131 (x0 : real -> Prop) (x1 : real) := ~ (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1).
Definition term115 (x0 : real -> Prop) (x1 : real) (x2 : real) := (~ (@IN real x1 x0)) \/ (real_le x1 x2).
Definition term20 (x0 : real -> Prop) := real_le (sup x0).
Definition term117 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (~ (@IN real y0 x0)) \/ (real_le y0 x1).
Definition term85 (x0 : real -> Prop) := fun y0 : real => (forall y1 : real, ((fun y2 : real => @IN real y2 x0) y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, ((fun y3 : real => @IN real y3 x0) y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term43 (x0 : real -> Prop) := fun y0 : real => (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) -> real_le y0 y1).
Definition term181 (x0 : real -> Prop) (x1 : real -> real) := (fun y0 : real -> real => forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) x1.
Definition term39 := forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (@ε real (fun y2 : real => (forall y3 : real, (@IN real y3 y0) -> real_le y3 y2) /\ (forall y3 : real, (forall y4 : real, (@IN real y4 y0) -> real_le y4 y3) -> real_le y2 y3)))) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (@ε real (fun y2 : real => (forall y3 : real, (@IN real y3 y0) -> real_le y3 y2) /\ (forall y3 : real, (forall y4 : real, (@IN real y4 y0) -> real_le y4 y3) -> real_le y2 y3))) y1).
Definition term38 := forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1).
Definition term28 (x0 : real -> Prop) := fun y0 : real => (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le (@ε real (fun y1 : real => (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (@IN real y3 x0) -> real_le y3 y2) -> real_le y1 y2))) y0.
Definition term126 (x0 : real -> Prop) := forall y0 : real, ~ (@IN real y0 x0).
Definition term94 (x0 : real) (x1 : real -> Prop) := (((~ (x1 = (@EMPTY real))) -> (forall y0 : real, (@IN real y0 x1) -> real_le y0 x0) -> (~ ((exists y0 : real, @IN real y0 x1) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x1) -> real_le y1 y0))) -> (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> False) -> (~ (x1 = (@EMPTY real))) -> (forall y0 : real, (@IN real y0 x1) -> real_le y0 x0) -> (~ ((exists y0 : real, @IN real y0 x1) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x1) -> real_le y1 y0))) -> (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> False) -> (~ (x1 = (@EMPTY real))) -> (forall y0 : real, (@IN real y0 x1) -> real_le y0 x0) -> (~ ((exists y0 : real, @IN real y0 x1) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x1) -> real_le y1 y0))) -> (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> False.
Definition term198 (x0 : real -> Prop) := and ((exists y0 : real, @IN real y0 x0) \/ (x0 = (@EMPTY real))).
Definition term102 (x0 : real) (x1 : real -> Prop) := (forall y0 : real, (@IN real y0 x1) -> real_le y0 x0) -> (~ ((exists y0 : real, @IN real y0 x1) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x1) -> real_le y1 y0))) -> ~ (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))).
Definition term182 (x0 : real -> Prop) := fun y0 : real -> real => (fun y1 : real -> real => forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) y0.
Definition term170 (x0 : real -> Prop) (x1 : real -> real) := forall y0 : real, (@IN real (x1 y0) x0) /\ (~ (real_le (x1 y0) y0)).
Definition term296 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term235 (x0 : real -> Prop) := @eq Prop ((exists y0 : real, @IN real y0 x0) \/ (x0 = (@EMPTY real))).
Definition term234 (x0 : real -> Prop) := @eq Prop ((exists y0 : real, (fun y1 : real => @IN real y1 x0) y0) \/ (x0 = (@EMPTY real))).
Definition term269 := (exists y0 : type1023, forall y1 : real -> Prop, (@IN real (y0 y1) y1) \/ (y1 = (@EMPTY real))) /\ (forall y0 : real -> Prop, (forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real)))).
Definition term288 := exists y0 : type1023, (forall y1 : real -> Prop, (@IN real (y0 y1) y1) \/ (y1 = (@EMPTY real))) /\ (forall y1 : real -> Prop, (forall y2 : real, ~ (@IN real y2 y1)) \/ (~ (y1 = (@EMPTY real)))).
Definition term161 (x0 : real -> Prop) := fun y0 : real => exists y1 : real, (fun y2 : real => fun y3 : real => (@IN real y3 x0) /\ (~ (real_le y3 y2))) y0 y1.
Definition term174 (x0 : real -> Prop) := (forall y0 : real, ~ (@IN real y0 x0)) \/ (exists y0 : real -> real, forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))).
Definition term217 := @eq Prop (forall y0 : real -> Prop, ((exists y1 : real, @IN real y1 y0) \/ (y0 = (@EMPTY real))) /\ ((forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real))))).
Definition term229 (x0 : real -> Prop) (x1 : Prop) := (exists y0 : real, x0 y0) \/ x1.
Definition term197 (x0 : real -> Prop) := and ((exists y0 : real, @IN real y0 x0) \/ (~ (~ (x0 = (@EMPTY real))))).
Definition term188 (x0 : real -> Prop) := fun y0 : real -> real => (forall y1 : real, ~ (@IN real y1 x0)) \/ ((fun y1 : real -> real => forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) y0).
Definition term192 (x0 : real -> Prop) := (~ (exists y0 : real, @IN real y0 x0)) \/ (~ (x0 = (@EMPTY real))).
Definition term103 (x0 : real -> Prop) := imp (~ (x0 = (@EMPTY real))).
Definition term231 (x0 : real -> Prop) := (exists y0 : real, (fun y1 : real => @IN real y1 x0) y0) \/ (x0 = (@EMPTY real)).
Definition term108 (x0 : real -> Prop) := forall y0 : real, (~ (x0 = (@EMPTY real))) -> (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> (~ ((exists y1 : real, @IN real y1 x0) /\ (exists y1 : real, forall y2 : real, (@IN real y2 x0) -> real_le y2 y1))) -> ~ (forall y1 : real -> Prop, (exists y2 : real, @IN real y2 y1) = (~ (y1 = (@EMPTY real)))).
Definition term107 (x0 : real -> Prop) := forall y0 : real, (~ (x0 = (@EMPTY real))) -> (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> (~ ((exists y1 : real, @IN real y1 x0) /\ (exists y1 : real, forall y2 : real, (@IN real y2 x0) -> real_le y2 y1))) -> (forall y1 : real -> Prop, (exists y2 : real, @IN real y2 y1) = (~ (y1 = (@EMPTY real)))) -> False.
Definition term97 := ~ (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))).
Definition term168 (x0 : real -> Prop) (x1 : real -> real) := fun y0 : real => (@IN real (x1 y0) x0) /\ (~ (real_le (x1 y0) y0)).
Definition term264 (x0 : type1023) := forall y0 : real -> Prop, (@IN real (x0 y0) y0) \/ (y0 = (@EMPTY real)).
Definition term301 (x0 : Prop) := (~ x0) -> x0.
Definition term195 (x0 : real -> Prop) := (exists y0 : real, @IN real y0 x0) \/ (~ (~ (x0 = (@EMPTY real)))).
Definition term106 (x0 : real -> Prop) := fun y0 : real => (~ (x0 = (@EMPTY real))) -> (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> (~ ((exists y1 : real, @IN real y1 x0) /\ (exists y1 : real, forall y2 : real, (@IN real y2 x0) -> real_le y2 y1))) -> ~ (forall y1 : real -> Prop, (exists y2 : real, @IN real y2 y1) = (~ (y1 = (@EMPTY real)))).
Definition term178 (x0 : Prop) (x1 : type1028) := exists y0 : real -> real, x0 \/ (x1 y0).
Definition term27 (x0 : real -> Prop) := fun y0 : real => (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le (sup x0) y0.
Definition term33 (x0 : real -> Prop) := imp ((~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)).
Definition term186 (x0 : real -> Prop) (x1 : real -> real) := (forall y0 : real, ~ (@IN real y0 x0)) \/ ((fun y0 : real -> real => forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))) x1).
Definition term44 (x0 : real -> Prop) := @eq Prop ((fun y0 : real => (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) -> real_le y0 y1)) (@ε real (fun y0 : real => (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) -> real_le y0 y1)))).
Definition term149 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term66 (x0 : real -> Prop) (x1 : real) := forall y0 : real, ((fun y1 : real => @IN real y1 x0) y0) -> real_le y0 x1.
Definition term60 (x0 : real -> Prop) := and (exists y0 : real, @IN real y0 x0).
Definition term267 := exists y0 : type1023, forall y1 : real -> Prop, (@IN real (y0 y1) y1) \/ (y1 = (@EMPTY real)).
Definition term248 := exists y0 : type1023, forall y1 : real -> Prop, (fun y2 : real -> Prop => fun y3 : real => (@IN real y3 y2) \/ (y2 = (@EMPTY real))) y1 (y0 y1).
Definition term246 (x0 : type1020) := exists y0 : type1023, forall y1 : real -> Prop, x0 y1 (y0 y1).
Definition term173 (x0 : real -> Prop) := exists y0 : real -> real, forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1)).
Definition term154 (x0 : real -> Prop) := exists y0 : real -> real, forall y1 : real, (fun y2 : real => fun y3 : real => (@IN real y3 x0) /\ (~ (real_le y3 y2))) y1 (y0 y1).
Definition term152 (x0 : type1626) := exists y0 : real -> real, forall y1 : real, x0 y1 (y0 y1).
Definition term119 (x0 : real -> Prop) := forall y0 : real, ~ (x0 y0).
Definition term297 (x0 : type1023) (x1 : real -> Prop) := (~ (x1 = (@EMPTY real))) -> @IN real (x0 x1) x1.
Definition term204 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term233 (x0 : real -> Prop) := or (exists y0 : real, (fun y1 : real => @IN real y1 x0) y0).
Definition term308 (x0 : real) (x1 : real) (x2 : real -> Prop) := (real_le x1 x0) \/ (~ (@IN real x1 x2)).
Definition term167 (x0 : real -> Prop) (x1 : real -> real) := fun y0 : real => (fun y1 : real => fun y2 : real => (@IN real y2 x0) /\ (~ (real_le y2 y1))) y0 (x1 y0).
Definition term166 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (@IN real (x1 x2) x0) /\ (~ (real_le (x1 x2) x2)).
Definition term104 (x0 : real) (x1 : real -> Prop) := (~ (x1 = (@EMPTY real))) -> (forall y0 : real, (@IN real y0 x1) -> real_le y0 x0) -> (~ ((exists y0 : real, @IN real y0 x1) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x1) -> real_le y1 y0))) -> ~ (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))).
Definition term71 (x0 : real -> Prop) := (exists y0 : real, @IN real y0 x0) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0).
Definition term220 := forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) \/ (y0 = (@EMPTY real)).
Definition term251 (x0 : real -> Prop) (x1 : real) := (fun y0 : real -> Prop => fun y1 : real => (@IN real y1 y0) \/ (y0 = (@EMPTY real))) x0 x1.
Definition term237 (x0 : real) (x1 : real -> Prop) := or (@IN real x0 x1).
Definition term250 (x0 : real -> Prop) := (fun y0 : real -> Prop => fun y1 : real => (@IN real y1 y0) \/ (y0 = (@EMPTY real))) x0.
Definition term55 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => @IN real y0 x0) x1.
Definition term132 (x0 : real -> Prop) (x1 : real) := exists y0 : real, ~ ((fun y1 : real => (@IN real y1 x0) -> real_le y1 x1) y0).
Definition term41 (x0 : real -> Prop) := (fun y0 : real => (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) -> real_le y0 y1)) (@ε real (fun y0 : real => (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) -> real_le y0 y1))).
Definition term319 (x0 : real -> Prop) := (fun y0 : real -> Prop => forall y1 : real, (~ (y0 = (@EMPTY real))) -> (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> (~ ((exists y2 : real, @IN real y2 y0) /\ (exists y2 : real, forall y3 : real, (@IN real y3 y0) -> real_le y3 y2))) -> (forall y2 : real -> Prop, (exists y3 : real, @IN real y3 y2) = (~ (y2 = (@EMPTY real)))) -> False) x0.
Definition term177 (x0 : Prop) (x1 : type1028) := x0 \/ (exists y0 : real -> real, x1 y0).
Definition term133 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (@IN real y0 x0) -> real_le y0 x1) x2.
Definition term138 (x0 : real -> Prop) := ~ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0).
Definition term164 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (fun y0 : real => fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 y0))) x2 (x1 x2).
Definition term305 (x0 : real -> real) (x1 : real) (x2 : real -> Prop) := @IN real (x0 x1) x2.
Definition term13 (x0 : real) (x1 : real -> Prop) := (@IN real x0 x1) -> real_le x0 (@ε real (fun y0 : real => (forall y1 : real, (@IN real y1 x1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 x1) -> real_le y2 y1) -> real_le y0 y1))).
Definition term285 (x0 : type1023) := (forall y0 : real -> Prop, (@IN real (x0 y0) y0) \/ (y0 = (@EMPTY real))) /\ (forall y0 : real -> Prop, (forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real)))).
Definition term226 := (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) \/ (y0 = (@EMPTY real))) /\ (forall y0 : real -> Prop, (forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real)))).
Definition term179 (x0 : real -> Prop) := (forall y0 : real, ~ (@IN real y0 x0)) \/ (exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) y0).
Definition term142 (x0 : real -> Prop) := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) y0).
Definition term255 := fun y0 : real -> Prop => exists y1 : real, (fun y2 : real -> Prop => fun y3 : real => (@IN real y3 y2) \/ (y2 = (@EMPTY real))) y0 y1.
Definition term143 (x0 : real -> Prop) := fun y0 : real => exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0)).
Definition term307 (x0 : real -> real) (x1 : real) (x2 : real -> Prop) := ~ (@IN real (x0 x1) x2).
Definition term274 := (exists y0 : type1023, (fun y1 : type1023 => forall y2 : real -> Prop, (@IN real (y1 y2) y2) \/ (y2 = (@EMPTY real))) y0) /\ (forall y0 : real -> Prop, (forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real)))).
Definition term298 (x0 : type1023) (x1 : real -> Prop) := @IN real (x0 x1) x1.
Definition term190 (x0 : real -> Prop) := exists y0 : real -> real, (forall y1 : real, ~ (@IN real y1 x0)) \/ (forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))).
Definition term46 (x0 : real -> Prop) := ((~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)) -> exists y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) -> real_le y0 y1).
Definition term52 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (@IN real y0 x0) -> real_le y0 x1.
Definition term275 := exists y0 : type1023, ((fun y1 : type1023 => forall y2 : real -> Prop, (@IN real (y1 y2) y2) \/ (y2 = (@EMPTY real))) y0) /\ (forall y1 : real -> Prop, (forall y2 : real, ~ (@IN real y2 y1)) \/ (~ (y1 = (@EMPTY real)))).
Definition term311 (x0 : real -> Prop) (x1 : real) (x2 : real) := (~ (~ (@IN real x1 x0))) -> real_le x1 x2.
Definition term278 := exists y0 : type1023, (fun y1 : type1023 => forall y2 : real -> Prop, (@IN real (y1 y2) y2) \/ (y2 = (@EMPTY real))) y0.
Definition term183 (x0 : real -> Prop) := exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) y0.
Definition term47 := fun y0 : real -> Prop => ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> exists y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (@IN real y3 y0) -> real_le y3 y2) -> real_le y1 y2).
Definition term91 := forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real))).
Definition term247 := forall y0 : real -> Prop, exists y1 : real, (fun y2 : real -> Prop => fun y3 : real => (@IN real y3 y2) \/ (y2 = (@EMPTY real))) y0 y1.
Definition term245 (x0 : type1020) := forall y0 : real -> Prop, exists y1 : real, x0 y0 y1.
Definition term95 (x0 : real) (x1 : real -> Prop) := (((~ (x1 = (@EMPTY real))) -> (forall y0 : real, (@IN real y0 x1) -> real_le y0 x0) -> (~ ((exists y0 : real, @IN real y0 x1) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x1) -> real_le y1 y0))) -> (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> False) -> (~ (x1 = (@EMPTY real))) -> (forall y0 : real, (@IN real y0 x1) -> real_le y0 x0) -> (~ ((exists y0 : real, @IN real y0 x1) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x1) -> real_le y1 y0))) -> (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> False) -> ((~ (x1 = (@EMPTY real))) -> (forall y0 : real, (@IN real y0 x1) -> real_le y0 x0) -> (~ ((exists y0 : real, @IN real y0 x1) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x1) -> real_le y1 y0))) -> (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> False) -> (~ (x1 = (@EMPTY real))) -> (forall y0 : real, (@IN real y0 x1) -> real_le y0 x0) -> (~ ((exists y0 : real, @IN real y0 x1) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x1) -> real_le y1 y0))) -> (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> False.
Definition term82 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le x1 y0.
Definition term81 (x0 : real -> Prop) (x1 : real) := forall y0 : real, (forall y1 : real, ((fun y2 : real => @IN real y2 x0) y1) -> real_le y1 y0) -> real_le x1 y0.
Definition term205 (x0 : type1022) (x1 : type1022) := forall y0 : real -> Prop, (x0 y0) /\ (x1 y0).
Definition term230 (x0 : real -> Prop) (x1 : Prop) := exists y0 : real, (x0 y0) \/ x1.
Definition term209 := fun y0 : real -> Prop => (exists y1 : real, @IN real y1 y0) \/ (y0 = (@EMPTY real)).
Definition term123 (x0 : real) (x1 : real -> Prop) := ~ (@IN real x0 x1).
Definition term3 (x0 : real -> Prop) := (exists y0 : real, x0 y0) /\ (exists y0 : real, forall y1 : real, (x0 y1) -> real_le y1 y0).
Definition term30 (x0 : real -> Prop) := forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le (@ε real (fun y1 : real => (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (@IN real y3 x0) -> real_le y3 y2) -> real_le y1 y2))) y0.
Definition term29 (x0 : real -> Prop) := forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le (sup x0) y0.
Definition term124 (x0 : real -> Prop) := fun y0 : real => ~ ((fun y1 : real => @IN real y1 x0) y0).
Definition term257 := @eq Prop (forall y0 : real -> Prop, exists y1 : real, (@IN real y1 y0) \/ (y0 = (@EMPTY real))).
Definition term256 := @eq Prop (forall y0 : real -> Prop, exists y1 : real, (fun y2 : real -> Prop => fun y3 : real => (@IN real y3 y2) \/ (y2 = (@EMPTY real))) y0 y1).
Definition term163 (x0 : real -> Prop) := @eq Prop (forall y0 : real, exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0))).
Definition term162 (x0 : real -> Prop) := @eq Prop (forall y0 : real, exists y1 : real, (fun y2 : real => fun y3 : real => (@IN real y3 x0) /\ (~ (real_le y3 y2))) y0 y1).
Definition term253 (x0 : real -> Prop) := fun y0 : real => (fun y1 : real -> Prop => fun y2 : real => (@IN real y2 y1) \/ (y1 = (@EMPTY real))) x0 y0.
Definition term176 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term194 (x0 : real -> Prop) := or (exists y0 : real, @IN real y0 x0).
Definition term146 (x0 : real -> Prop) := or (forall y0 : real, ~ (@IN real y0 x0)).
Definition term224 := forall y0 : real -> Prop, (fun y1 : real -> Prop => (forall y2 : real, ~ (@IN real y2 y1)) \/ (~ (y1 = (@EMPTY real)))) y0.
Definition term219 := forall y0 : real -> Prop, (fun y1 : real -> Prop => (exists y2 : real, @IN real y2 y1) \/ (y1 = (@EMPTY real))) y0.
Definition term254 (x0 : real -> Prop) := exists y0 : real, (fun y1 : real -> Prop => fun y2 : real => (@IN real y2 y1) \/ (y1 = (@EMPTY real))) x0 y0.
Definition term318 (x0 : real -> real) (x1 : real) := (real_le (x0 x1) x1) -> False.
Definition term290 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => ~ (@IN real y0 x0)) x1.
Definition term185 (x0 : real -> Prop) := @eq Prop ((forall y0 : real, ~ (@IN real y0 x0)) \/ (exists y0 : real -> real, forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1)))).
Definition term184 (x0 : real -> Prop) := @eq Prop ((forall y0 : real, ~ (@IN real y0 x0)) \/ (exists y0 : real -> real, (fun y1 : real -> real => forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) y0)).
Definition term87 (x0 : real -> Prop) := ((exists y0 : real, @IN real y0 x0) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)) -> exists y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) -> real_le y0 y1).
Definition term53 (x0 : real -> Prop) := ((exists y0 : real, (fun y1 : real => @IN real y1 x0) y0) /\ (exists y0 : real, forall y1 : real, ((fun y2 : real => @IN real y2 x0) y1) -> real_le y1 y0)) -> exists y0 : real, (forall y1 : real, ((fun y2 : real => @IN real y2 x0) y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, ((fun y3 : real => @IN real y3 x0) y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term2 (x0 : real -> Prop) := ((exists y0 : real, x0 y0) /\ (exists y0 : real, forall y1 : real, (x0 y1) -> real_le y1 y0)) -> exists y0 : real, (forall y1 : real, (x0 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x0 y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term84 (x0 : real -> Prop) (x1 : real) := (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le x1 y0).
Definition term83 (x0 : real -> Prop) (x1 : real) := (forall y0 : real, ((fun y1 : real => @IN real y1 x0) y0) -> real_le y0 x1) /\ (forall y0 : real, (forall y1 : real, ((fun y2 : real => @IN real y2 x0) y1) -> real_le y1 y0) -> real_le x1 y0).
Definition term32 (x0 : real -> Prop) := (forall y0 : real, (@IN real y0 x0) -> real_le y0 (@ε real (fun y1 : real => (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (@IN real y3 x0) -> real_le y3 y2) -> real_le y1 y2)))) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le (@ε real (fun y1 : real => (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (@IN real y3 x0) -> real_le y3 y2) -> real_le y1 y2))) y0).
Definition term31 (x0 : real -> Prop) := (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le (sup x0) y0).
Definition term92 (x0 : real) (x1 : real -> Prop) := (~ (x1 = (@EMPTY real))) -> (forall y0 : real, (@IN real y0 x1) -> real_le y0 x0) -> (~ ((exists y0 : real, @IN real y0 x1) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x1) -> real_le y1 y0))) -> (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> False.
Definition term73 (x0 : real -> Prop) := imp ((exists y0 : real, @IN real y0 x0) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)).
Definition term72 (x0 : real -> Prop) := imp ((exists y0 : real, (fun y1 : real => @IN real y1 x0) y0) /\ (exists y0 : real, forall y1 : real, ((fun y2 : real => @IN real y2 x0) y1) -> real_le y1 y0)).
Definition term175 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term279 := and (exists y0 : type1023, (fun y1 : type1023 => forall y2 : real -> Prop, (@IN real (y1 y2) y2) \/ (y2 = (@EMPTY real))) y0).
Definition term271 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term157 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 y0))) x1 x2.
Definition term118 (x0 : real -> Prop) := ~ (ex x0).
Definition term266 := fun y0 : type1023 => forall y1 : real -> Prop, (@IN real (y0 y1) y1) \/ (y1 = (@EMPTY real)).
Definition term284 (x0 : type1023) := ((fun y0 : type1023 => forall y1 : real -> Prop, (@IN real (y0 y1) y1) \/ (y1 = (@EMPTY real))) x0) /\ (forall y0 : real -> Prop, (forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real)))).
Definition term153 (x0 : real -> Prop) := forall y0 : real, exists y1 : real, (fun y2 : real => fun y3 : real => (@IN real y3 x0) /\ (~ (real_le y3 y2))) y0 y1.
Definition term151 (x0 : type1626) := forall y0 : real, exists y1 : real, x0 y0 y1.
Definition term144 (x0 : real -> Prop) := forall y0 : real, exists y1 : real, (@IN real y1 x0) /\ (~ (real_le y1 y0)).
Definition term193 (x0 : real -> Prop) := (forall y0 : real, ~ (@IN real y0 x0)) \/ (~ (x0 = (@EMPTY real))).
Definition term292 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (fun y0 : real => (@IN real (x1 y0) x0) /\ (~ (real_le (x1 y0) y0))) x2.
Definition term282 (x0 : type1023) := and ((fun y0 : type1023 => forall y1 : real -> Prop, (@IN real (y0 y1) y1) \/ (y1 = (@EMPTY real))) x0).
Definition term238 (x0 : real) (x1 : real -> Prop) := ((fun y0 : real => @IN real y0 x1) x0) \/ (x1 = (@EMPTY real)).
Definition term51 (x0 : real -> Prop) := ~ (x0 = (@EMPTY real)).
Definition term273 (x0 : type257) (x1 : Prop) := exists y0 : type1023, (x0 y0) /\ x1.
Definition term14 (x0 : real -> Prop) := fun y0 : real => (@IN real y0 x0) -> real_le y0 (sup x0).
Definition term12 (x0 : real) (x1 : real -> Prop) := (@IN real x0 x1) -> real_le x0 (sup x1).
Definition term22 (x0 : real -> Prop) (x1 : real) := real_le (sup x0) x1.
Definition term68 (x0 : real -> Prop) := fun y0 : real => forall y1 : real, (@IN real y1 x0) -> real_le y1 y0.
Definition term67 (x0 : real -> Prop) := fun y0 : real => forall y1 : real, ((fun y2 : real => @IN real y2 x0) y1) -> real_le y1 y0.
Definition term165 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (fun y0 : real => (@IN real y0 x0) /\ (~ (real_le y0 x2))) (x1 x2).
Definition term130 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term96 := (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> False.
Definition term134 (x0 : real -> Prop) (x1 : real) (x2 : real) := ~ ((fun y0 : real => (@IN real y0 x0) -> real_le y0 x1) x2).
Definition term78 (x0 : real -> Prop) (x1 : real) (x2 : real) := (forall y0 : real, (@IN real y0 x0) -> real_le y0 x2) -> real_le x1 x2.
Definition term77 (x0 : real -> Prop) (x1 : real) (x2 : real) := (forall y0 : real, ((fun y1 : real => @IN real y1 x0) y0) -> real_le y0 x2) -> real_le x1 x2.
Definition term228 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term11 (x0 : real) (x1 : real -> Prop) := imp (@IN real x0 x1).
Definition term243 := fun y0 : real -> Prop => exists y1 : real, (@IN real y1 y0) \/ (y0 = (@EMPTY real)).
Definition term202 := forall y0 : real -> Prop, ((exists y1 : real, @IN real y1 y0) \/ (y0 = (@EMPTY real))) /\ ((forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real)))).
Definition term313 (x0 : real) (x1 : real -> Prop) := ~ (~ (@IN real x0 x1)).
Definition term223 := fun y0 : real -> Prop => (fun y1 : real -> Prop => (forall y2 : real, ~ (@IN real y2 y1)) \/ (~ (y1 = (@EMPTY real)))) y0.
Definition term86 (x0 : real -> Prop) := exists y0 : real, (forall y1 : real, ((fun y2 : real => @IN real y2 x0) y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, ((fun y3 : real => @IN real y3 x0) y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term42 (x0 : real -> Prop) := exists y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) -> real_le y0 y1).
Definition term4 (x0 : real -> Prop) := exists y0 : real, (forall y1 : real, (x0 y1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (x0 y2) -> real_le y2 y1) -> real_le y0 y1).
Definition term216 := @eq Prop (forall y0 : real -> Prop, ((fun y1 : real -> Prop => (exists y2 : real, @IN real y2 y1) \/ (y1 = (@EMPTY real))) y0) /\ ((fun y1 : real -> Prop => (forall y2 : real, ~ (@IN real y2 y1)) \/ (~ (y1 = (@EMPTY real)))) y0)).
Definition term259 (x0 : type1023) (x1 : real -> Prop) := (fun y0 : real => (@IN real y0 x1) \/ (x1 = (@EMPTY real))) (x0 x1).
Definition term316 (x0 : real -> real) (x1 : real) := real_le (x0 x1) x1.
Definition term63 (x0 : real -> Prop) (x1 : real) (x2 : real) := (@IN real x1 x0) -> real_le x1 x2.
Definition term302 (x0 : real) (x1 : real -> Prop) := (@IN real x0 x1) -> False.
Definition term26 (x0 : real -> Prop) (x1 : real) := (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1) -> real_le (@ε real (fun y0 : real => (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) -> real_le y0 y1))) x1.
Definition term37 := fun y0 : real -> Prop => ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (@ε real (fun y2 : real => (forall y3 : real, (@IN real y3 y0) -> real_le y3 y2) /\ (forall y3 : real, (forall y4 : real, (@IN real y4 y0) -> real_le y4 y3) -> real_le y2 y3)))) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (@ε real (fun y2 : real => (forall y3 : real, (@IN real y3 y0) -> real_le y3 y2) /\ (forall y3 : real, (forall y4 : real, (@IN real y4 y0) -> real_le y4 y3) -> real_le y2 y3))) y1).
Definition term36 := fun y0 : real -> Prop => ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> (forall y1 : real, (@IN real y1 y0) -> real_le y1 (sup y0)) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> real_le (sup y0) y1).
Definition term25 (x0 : real -> Prop) (x1 : real) := (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1) -> real_le (sup x0) x1.
Definition term21 (x0 : real -> Prop) := real_le (@ε real (fun y0 : real => (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) -> real_le y0 y1))).
Definition term61 (x0 : real -> Prop) (x1 : real) := imp ((fun y0 : real => @IN real y0 x0) x1).
Definition term100 (x0 : real -> Prop) := (~ ((exists y0 : real, @IN real y0 x0) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0))) -> ~ (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))).
Definition term276 (x0 : type1023) := (fun y0 : type1023 => forall y1 : real -> Prop, (@IN real (y0 y1) y1) \/ (y1 = (@EMPTY real))) x0.
Definition term140 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) x1.
Definition term289 (x0 : type1023) (x1 : real -> Prop) := (fun y0 : real -> Prop => (@IN real (x0 y0) y0) \/ (y0 = (@EMPTY real))) x1.
Definition term122 (x0 : real -> Prop) (x1 : real) := ~ ((fun y0 : real => @IN real y0 x0) x1).
Definition term213 (x0 : real -> Prop) := (fun y0 : real -> Prop => (forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real)))) x0.
Definition term70 (x0 : real -> Prop) := (exists y0 : real, (fun y1 : real => @IN real y1 x0) y0) /\ (exists y0 : real, forall y1 : real, ((fun y2 : real => @IN real y2 x0) y1) -> real_le y1 y0).
Definition term218 := fun y0 : real -> Prop => (fun y1 : real -> Prop => (exists y2 : real, @IN real y2 y1) \/ (y1 = (@EMPTY real))) y0.
Definition term249 := fun y0 : real -> Prop => fun y1 : real => (@IN real y1 y0) \/ (y0 = (@EMPTY real)).
Definition term147 (x0 : real -> Prop) := (~ (exists y0 : real, @IN real y0 x0)) \/ (~ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)).
Definition term159 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (fun y1 : real => fun y2 : real => (@IN real y2 x0) /\ (~ (real_le y2 y1))) x1 y0.
Definition term48 := forall y0 : real -> Prop, ((~ (y0 = (@EMPTY real))) /\ (exists y1 : real, forall y2 : real, (@IN real y2 y0) -> real_le y2 y1)) -> exists y1 : real, (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (@IN real y3 y0) -> real_le y3 y2) -> real_le y1 y2).
Definition term0 := forall y0 : real -> Prop, ((exists y1 : real, y0 y1) /\ (exists y1 : real, forall y2 : real, (y0 y2) -> real_le y2 y1)) -> exists y1 : real, (forall y2 : real, (y0 y2) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (y0 y3) -> real_le y3 y2) -> real_le y1 y2).
Definition term210 := fun y0 : real -> Prop => (forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real))).
Definition term169 (x0 : real -> Prop) (x1 : real -> real) := forall y0 : real, (fun y1 : real => fun y2 : real => (@IN real y2 x0) /\ (~ (real_le y2 y1))) y0 (x1 y0).
Definition term258 (x0 : type1023) (x1 : real -> Prop) := (fun y0 : real -> Prop => fun y1 : real => (@IN real y1 y0) \/ (y0 = (@EMPTY real))) x1 (x0 x1).
Definition term252 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => (@IN real y0 x0) \/ (x0 = (@EMPTY real))) x1.
Definition term263 (x0 : type1023) := forall y0 : real -> Prop, (fun y1 : real -> Prop => fun y2 : real => (@IN real y2 y1) \/ (y1 = (@EMPTY real))) y0 (x0 y0).
Definition term112 := forall y0 : real -> Prop, forall y1 : real, (~ (y0 = (@EMPTY real))) -> (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> (~ ((exists y2 : real, @IN real y2 y0) /\ (exists y2 : real, forall y3 : real, (@IN real y3 y0) -> real_le y3 y2))) -> ~ (forall y2 : real -> Prop, (exists y3 : real, @IN real y3 y2) = (~ (y2 = (@EMPTY real)))).
Definition term111 := forall y0 : real -> Prop, forall y1 : real, (~ (y0 = (@EMPTY real))) -> (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> (~ ((exists y2 : real, @IN real y2 y0) /\ (exists y2 : real, forall y3 : real, (@IN real y3 y0) -> real_le y3 y2))) -> (forall y2 : real -> Prop, (exists y3 : real, @IN real y3 y2) = (~ (y2 = (@EMPTY real)))) -> False.
Definition term272 (x0 : type257) (x1 : Prop) := (exists y0 : type1023, x0 y0) /\ x1.
Definition term300 (x0 : type1023) (x1 : real -> Prop) := ~ (@IN real (x0 x1) x1).
Definition term23 (x0 : real -> Prop) (x1 : real) := real_le (@ε real (fun y0 : real => (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) -> real_le y0 y1))) x1.
Definition term225 := forall y0 : real -> Prop, (forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real))).
Definition term315 (x0 : real -> Prop) (x1 : real -> real) (x2 : real) := (@IN real (x1 x2) x0) -> real_le (x1 x2) x2.
Definition term214 (x0 : real -> Prop) := ((fun y0 : real -> Prop => (exists y1 : real, @IN real y1 y0) \/ (y0 = (@EMPTY real))) x0) /\ ((fun y0 : real -> Prop => (forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real)))) x0).
Definition term262 (x0 : type1023) := fun y0 : real -> Prop => (@IN real (x0 y0) y0) \/ (y0 = (@EMPTY real)).
Definition term201 := fun y0 : real -> Prop => ((exists y1 : real, @IN real y1 y0) \/ (y0 = (@EMPTY real))) /\ ((forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real)))).
Definition term105 (x0 : real -> Prop) := fun y0 : real => (~ (x0 = (@EMPTY real))) -> (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> (~ ((exists y1 : real, @IN real y1 x0) /\ (exists y1 : real, forall y2 : real, (@IN real y2 x0) -> real_le y2 y1))) -> (forall y1 : real -> Prop, (exists y2 : real, @IN real y2 y1) = (~ (y1 = (@EMPTY real)))) -> False.
Definition term141 (x0 : real -> Prop) (x1 : real) := ~ ((fun y0 : real => forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) x1).
Definition term283 (x0 : type1023) := and (forall y0 : real -> Prop, (@IN real (x0 y0) y0) \/ (y0 = (@EMPTY real))).
Definition term222 := and (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) \/ (y0 = (@EMPTY real))).
Definition term172 (x0 : real -> Prop) := fun y0 : real -> real => forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1)).
Definition term171 (x0 : real -> Prop) := fun y0 : real -> real => forall y1 : real, (fun y2 : real => fun y3 : real => (@IN real y3 x0) /\ (~ (real_le y3 y2))) y1 (y0 y1).
Definition term110 := fun y0 : real -> Prop => forall y1 : real, (~ (y0 = (@EMPTY real))) -> (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> (~ ((exists y2 : real, @IN real y2 y0) /\ (exists y2 : real, forall y3 : real, (@IN real y3 y0) -> real_le y3 y2))) -> ~ (forall y2 : real -> Prop, (exists y3 : real, @IN real y3 y2) = (~ (y2 = (@EMPTY real)))).
Definition term109 := fun y0 : real -> Prop => forall y1 : real, (~ (y0 = (@EMPTY real))) -> (forall y2 : real, (@IN real y2 y0) -> real_le y2 y1) -> (~ ((exists y2 : real, @IN real y2 y0) /\ (exists y2 : real, forall y3 : real, (@IN real y3 y0) -> real_le y3 y2))) -> (forall y2 : real -> Prop, (exists y3 : real, @IN real y3 y2) = (~ (y2 = (@EMPTY real)))) -> False.
Definition term199 (x0 : real -> Prop) := ((exists y0 : real, @IN real y0 x0) \/ (~ (~ (x0 = (@EMPTY real))))) /\ ((~ (exists y0 : real, @IN real y0 x0)) \/ (~ (x0 = (@EMPTY real)))).
Definition term310 (x0 : real) (x1 : real) (x2 : real -> Prop) := @eq Prop ((real_le x1 x0) \/ (~ (@IN real x1 x2))).
Definition term120 (x0 : real -> Prop) := ~ (exists y0 : real, @IN real y0 x0).
Definition term137 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (@IN real y0 x0) /\ (~ (real_le y0 x1)).
Definition term239 (x0 : real) (x1 : real -> Prop) := (@IN real x0 x1) \/ (x1 = (@EMPTY real)).
Definition term125 (x0 : real -> Prop) := fun y0 : real => ~ (@IN real y0 x0).
Definition term189 (x0 : real -> Prop) := fun y0 : real -> real => (forall y1 : real, ~ (@IN real y1 x0)) \/ (forall y1 : real, (@IN real (y0 y1) x0) /\ (~ (real_le (y0 y1) y1))).
Definition term56 (x0 : real -> Prop) := fun y0 : real => (fun y1 : real => @IN real y1 x0) y0.
Definition term58 (x0 : real -> Prop) := exists y0 : real, @IN real y0 x0.
Definition term8 (x0 : real -> Prop) := @ε real (fun y0 : real => (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) -> real_le y0 y1)).
Definition term208 := (forall y0 : real -> Prop, (fun y1 : real -> Prop => (exists y2 : real, @IN real y2 y1) \/ (y1 = (@EMPTY real))) y0) /\ (forall y0 : real -> Prop, (fun y1 : real -> Prop => (forall y2 : real, ~ (@IN real y2 y1)) \/ (~ (y1 = (@EMPTY real)))) y0).
Definition term59 (x0 : real -> Prop) := and (exists y0 : real, (fun y1 : real => @IN real y1 x0) y0).
Definition term155 (x0 : real -> Prop) := fun y0 : real => fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 y0)).
Definition term158 (x0 : real -> Prop) (x1 : real) (x2 : real) := (fun y0 : real => (@IN real y0 x0) /\ (~ (real_le y0 x1))) x2.
Definition term139 (x0 : real -> Prop) := forall y0 : real, ~ ((fun y1 : real => forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) y0).
Definition term121 (x0 : real -> Prop) := forall y0 : real, ~ ((fun y1 : real => @IN real y1 x0) y0).
Definition term76 (x0 : real -> Prop) (x1 : real) := imp (forall y0 : real, ((fun y1 : real => @IN real y1 x0) y0) -> real_le y0 x1).
Definition term24 (x0 : real -> Prop) (x1 : real) := imp (forall y0 : real, (@IN real y0 x0) -> real_le y0 x1).
Definition term261 (x0 : type1023) := fun y0 : real -> Prop => (fun y1 : real -> Prop => fun y2 : real => (@IN real y2 y1) \/ (y1 = (@EMPTY real))) y0 (x0 y0).
Definition term317 (x0 : real -> real) (x1 : real) := (~ (real_le (x0 x1) x1)) -> real_le (x0 x1) x1.
Definition term135 (x0 : real -> Prop) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => (@IN real y1 x0) -> real_le y1 x1) y0).
Definition term16 (x0 : real -> Prop) := forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0).
Definition term128 (x0 : real -> Prop) (x1 : real) (x2 : real) := (@IN real x1 x0) /\ (~ (real_le x1 x2)).
Definition term54 (x0 : real -> Prop) := fun y0 : real => @IN real y0 x0.
Definition term221 := and (forall y0 : real -> Prop, (fun y1 : real -> Prop => (exists y2 : real, @IN real y2 y1) \/ (y1 = (@EMPTY real))) y0).
Definition term203 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term101 (x0 : real) (x1 : real -> Prop) := (forall y0 : real, (@IN real y0 x1) -> real_le y0 x0) -> (~ ((exists y0 : real, @IN real y0 x1) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x1) -> real_le y1 y0))) -> (forall y0 : real -> Prop, (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real)))) -> False.
Definition term40 (x0 : real -> Prop) := x0 (@ε real x0).
Definition term232 (x0 : real -> Prop) := exists y0 : real, ((fun y1 : real => @IN real y1 x0) y0) \/ (x0 = (@EMPTY real)).
Definition term236 (x0 : real -> Prop) (x1 : real) := or ((fun y0 : real => @IN real y0 x0) x1).
Definition term309 (x0 : real -> Prop) (x1 : real) (x2 : real) := @eq Prop ((~ (@IN real x1 x0)) \/ (real_le x1 x2)).
Definition term156 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => fun y1 : real => (@IN real y1 x0) /\ (~ (real_le y1 y0))) x1.
Definition term281 := @eq Prop ((exists y0 : type1023, forall y1 : real -> Prop, (@IN real (y0 y1) y1) \/ (y1 = (@EMPTY real))) /\ (forall y0 : real -> Prop, (forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real))))).
Definition term280 := @eq Prop ((exists y0 : type1023, (fun y1 : type1023 => forall y2 : real -> Prop, (@IN real (y1 y2) y2) \/ (y2 = (@EMPTY real))) y0) /\ (forall y0 : real -> Prop, (forall y1 : real, ~ (@IN real y1 y0)) \/ (~ (y0 = (@EMPTY real))))).
Definition term277 := fun y0 : type1023 => (fun y1 : type1023 => forall y2 : real -> Prop, (@IN real (y1 y2) y2) \/ (y2 = (@EMPTY real))) y0.
Definition term62 (x0 : real -> Prop) (x1 : real) (x2 : real) := ((fun y0 : real => @IN real y0 x0) x1) -> real_le x1 x2.
Definition term196 (x0 : real -> Prop) := (exists y0 : real, @IN real y0 x0) \/ (x0 = (@EMPTY real)).
Definition term6 := (forall y0 : real -> Prop, ((exists y1 : real, y0 y1) /\ (exists y1 : real, forall y2 : real, (y0 y2) -> real_le y2 y1)) -> exists y1 : real, (forall y2 : real, (y0 y2) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (y0 y3) -> real_le y3 y2) -> real_le y1 y2)) -> forall y0 : real -> Prop, ((exists y1 : real, y0 y1) /\ (exists y1 : real, forall y2 : real, (y0 y2) -> real_le y2 y1)) -> exists y1 : real, (forall y2 : real, (y0 y2) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (y0 y3) -> real_le y3 y2) -> real_le y1 y2).
Definition term145 (x0 : real -> Prop) := or (~ (exists y0 : real, @IN real y0 x0)).
Definition term242 (x0 : real -> Prop) := exists y0 : real, (@IN real y0 x0) \/ (x0 = (@EMPTY real)).
Definition term270 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term89 (x0 : real -> Prop) := (~ ((exists y0 : real, @IN real y0 x0) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0))) -> False.
Definition term160 (x0 : real -> Prop) (x1 : real) := exists y0 : real, (fun y1 : real => fun y2 : real => (@IN real y2 x0) /\ (~ (real_le y2 y1))) x1 y0.
Definition term180 (x0 : real -> Prop) := exists y0 : real -> real, (forall y1 : real, ~ (@IN real y1 x0)) \/ ((fun y1 : real -> real => forall y2 : real, (@IN real (y1 y2) x0) /\ (~ (real_le (y1 y2) y2))) y0).
Definition term320 (x0 : real -> Prop) (x1 : real) := (fun y0 : real => (~ (x0 = (@EMPTY real))) -> (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> (~ ((exists y1 : real, @IN real y1 x0) /\ (exists y1 : real, forall y2 : real, (@IN real y2 x0) -> real_le y2 y1))) -> (forall y1 : real -> Prop, (exists y2 : real, @IN real y2 y1) = (~ (y1 = (@EMPTY real)))) -> False) x1.
Definition term136 (x0 : real -> Prop) (x1 : real) := fun y0 : real => (@IN real y0 x0) /\ (~ (real_le y0 x1)).
Definition term240 (x0 : real -> Prop) := fun y0 : real => ((fun y1 : real => @IN real y1 x0) y0) \/ (x0 = (@EMPTY real)).
Definition term114 := fun y0 : real -> Prop => (exists y1 : real, @IN real y1 y0) = (~ (y0 = (@EMPTY real))).
Definition term150 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term127 (x0 : real -> Prop) (x1 : real) (x2 : real) := ~ ((@IN real x1 x0) -> real_le x1 x2).
Definition term10 (x0 : real) (x1 : real -> Prop) := real_le x0 (@ε real (fun y0 : real => (forall y1 : real, (@IN real y1 x1) -> real_le y1 y0) /\ (forall y1 : real, (forall y2 : real, (@IN real y2 x1) -> real_le y2 y1) -> real_le y0 y1))).
Definition term207 := forall y0 : real -> Prop, ((fun y1 : real -> Prop => (exists y2 : real, @IN real y2 y1) \/ (y1 = (@EMPTY real))) y0) /\ ((fun y1 : real -> Prop => (forall y2 : real, ~ (@IN real y2 y1)) \/ (~ (y1 = (@EMPTY real)))) y0).
Definition term244 := forall y0 : real -> Prop, exists y1 : real, (@IN real y1 y0) \/ (y0 = (@EMPTY real)).
Definition term294 (x0 : real -> Prop) := (x0 = (@EMPTY real)) -> ~ (x0 = (@EMPTY real)).
Definition term206 (x0 : type1022) (x1 : type1022) := (forall y0 : real -> Prop, x0 y0) /\ (forall y0 : real -> Prop, x1 y0).
Definition term35 (x0 : real -> Prop) := ((~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)) -> (forall y0 : real, (@IN real y0 x0) -> real_le y0 (@ε real (fun y1 : real => (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (@IN real y3 x0) -> real_le y3 y2) -> real_le y1 y2)))) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le (@ε real (fun y1 : real => (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (@IN real y3 x0) -> real_le y3 y2) -> real_le y1 y2))) y0).
Definition term34 (x0 : real -> Prop) := ((~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)) -> (forall y0 : real, (@IN real y0 x0) -> real_le y0 (sup x0)) /\ (forall y0 : real, (forall y1 : real, (@IN real y1 x0) -> real_le y1 y0) -> real_le (sup x0) y0).
Definition term1 (x0 : real -> Prop) := (fun y0 : real -> Prop => ((exists y1 : real, y0 y1) /\ (exists y1 : real, forall y2 : real, (y0 y2) -> real_le y2 y1)) -> exists y1 : real, (forall y2 : real, (y0 y2) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (y0 y3) -> real_le y3 y2) -> real_le y1 y2)) x0.
Definition term287 := fun y0 : type1023 => (forall y1 : real -> Prop, (@IN real (y0 y1) y1) \/ (y1 = (@EMPTY real))) /\ (forall y1 : real -> Prop, (forall y2 : real, ~ (@IN real y2 y1)) \/ (~ (y1 = (@EMPTY real)))).
Definition term90 (x0 : real -> Prop) := ~ ((exists y0 : real, @IN real y0 x0) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0)).
Definition term295 (x0 : Prop) := x0 -> ~ x0.
Definition term303 (x0 : type1023) (x1 : real -> Prop) := (@IN real (x0 x1) x1) -> False.
Definition term49 (x0 : real -> Prop) := (~ (x0 = (@EMPTY real))) /\ (exists y0 : real, forall y1 : real, (@IN real y1 x0) -> real_le y1 y0).
Definition term314 (x0 : real) (x1 : real -> Prop) := imp (~ (~ (@IN real x0 x1))).
Definition term57 (x0 : real -> Prop) := exists y0 : real, (fun y1 : real => @IN real y1 x0) y0.
Definition term17 (x0 : real -> Prop) := forall y0 : real, (@IN real y0 x0) -> real_le y0 (@ε real (fun y1 : real => (forall y2 : real, (@IN real y2 x0) -> real_le y2 y1) /\ (forall y2 : real, (forall y3 : real, (@IN real y3 x0) -> real_le y3 y2) -> real_le y1 y2))).
