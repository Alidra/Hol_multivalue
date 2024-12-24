Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term15 (a0 : Type') (x0 : a0) := ~ (@IN a0 x0 (@EMPTY a0)).
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) := @IN nat x0 (dotdot x1 x2).
Definition term80 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term26 (x0 : nat) (x1 : nat) := fun y0 : nat => (@IN nat y0 (dotdot x0 x1)) = (@IN nat y0 (@EMPTY nat)).
Definition term161 (x0 : nat) (x1 : nat) := exists y0 : nat, ((fun y1 : nat => (Peano.le x1 y1) /\ (Peano.le y1 x0)) y0) /\ (Peano.lt x0 x1).
Definition term281 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0).
Definition term72 (x0 : nat -> Prop) := ~ (all x0).
Definition term320 := (~ False) -> False.
Definition term168 (x0 : nat) (x1 : nat) (x2 : nat) := and ((fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1)) x2).
Definition term74 (x0 : nat) (x1 : nat) := ~ (forall y0 : nat, ~ ((Peano.le x0 y0) /\ (Peano.le y0 x1))).
Definition term216 (x0 : nat) (x1 : nat) (x2 : nat) := ((forall y0 : nat, (~ (Peano.le x2 y0)) \/ (~ (Peano.le y0 x1))) /\ (~ (Peano.lt x1 x2))) \/ (((Peano.le x2 x0) /\ (Peano.le x0 x1)) /\ (Peano.lt x1 x2)).
Definition term224 (x0 : nat) (x1 : nat) (x2 : nat) := or (~ ((Peano.le x0 x1) /\ (Peano.le x1 x2))).
Definition term119 (x0 : nat) (x1 : nat) := or ((fun y0 : nat => (forall y1 : nat, (~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 y0))) /\ (~ (Peano.lt y0 x0))) x1).
Definition term273 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0).
Definition term250 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0) /\ ((fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0).
Definition term117 (x0 : nat) := fun y0 : nat => (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) /\ (Peano.lt y0 x0).
Definition term307 (x0 : Prop) := ~ (~ x0).
Definition term295 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y2))) \/ (Peano.le y0 y2)) x0.
Definition term7 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (@IN nat y2 (dotdot y0 y1)) = ((Peano.le y0 y2) /\ (Peano.le y2 y1))) x0.
Definition term91 (x0 : nat) (x1 : nat) := (forall y0 : nat, (~ (Peano.le x1 y0)) \/ (~ (Peano.le y0 x0))) /\ (~ (Peano.lt x0 x1)).
Definition term56 := (~ (forall y0 : nat, forall y1 : nat, (forall y2 : nat, ~ ((Peano.le y0 y2) /\ (Peano.le y2 y1))) = (Peano.lt y1 y0))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)).
Definition term78 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ ((fun y1 : nat => ~ ((Peano.le x0 y1) /\ (Peano.le y1 x1))) y0).
Definition term342 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) /\ (Peano.lt x0 x1).
Definition term259 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0) /\ ((fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0).
Definition term58 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term118 (x0 : nat) (x1 : nat) := (fun y0 : nat => (forall y1 : nat, (~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 y0))) /\ (~ (Peano.lt y0 x0))) x1.
Definition term77 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((fun y0 : nat => ~ ((Peano.le x0 y0) /\ (Peano.le y0 x1))) x2).
Definition term93 (x0 : nat) (x1 : nat) := or ((forall y0 : nat, (~ (Peano.le x1 y0)) \/ (~ (Peano.le y0 x0))) /\ (~ (Peano.lt x0 x1))).
Definition term92 (x0 : nat) (x1 : nat) := or ((forall y0 : nat, ~ ((Peano.le x1 y0) /\ (Peano.le y0 x0))) /\ (~ (Peano.lt x0 x1))).
Definition term298 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x1 x0)) \/ ((~ (Peano.le x0 x2)) \/ (Peano.le x1 x2)).
Definition term174 (x0 : nat) (x1 : nat) := exists y0 : nat, ((Peano.le x1 y0) /\ (Peano.le y0 x0)) /\ (Peano.lt x0 x1).
Definition term220 (x0 : nat) := fun y0 : nat => exists y1 : nat, ((forall y2 : nat, (~ (Peano.le x0 y2)) \/ (~ (Peano.le y2 y0))) /\ (~ (Peano.lt y0 x0))) \/ (((Peano.le x0 y1) /\ (Peano.le y1 y0)) /\ (Peano.lt y0 x0)).
Definition term108 := fun y0 : nat => exists y1 : nat, ((forall y2 : nat, (~ (Peano.le y0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 y0))) \/ ((exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 y0)).
Definition term129 (x0 : nat) := or (exists y0 : nat, (forall y1 : nat, (~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 y0))) /\ (~ (Peano.lt y0 x0))).
Definition term333 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (Peano.le x0 x1))) /\ (~ (~ (Peano.le x1 x2))).
Definition term133 (x0 : nat) := (exists y0 : nat, (forall y1 : nat, (~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 y0))) /\ (~ (Peano.lt y0 x0))) \/ (exists y0 : nat, (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) /\ (Peano.lt y0 x0)).
Definition term111 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term167 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (Peano.le x1 y0) /\ (Peano.le y0 x0)) /\ (Peano.lt x0 x1)).
Definition term166 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (Peano.le x1 y1) /\ (Peano.le y1 x0)) y0) /\ (Peano.lt x0 x1)).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term39 (x0 : Prop) := (~ x0) -> False.
Definition term274 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0).
Definition term251 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0) /\ (forall y0 : nat, (fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0).
Definition term292 := (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term243 (x0 : nat) := forall y0 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) /\ ((Peano.le x0 y0) \/ (Peano.lt y0 x0)).
Definition term336 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2)))).
Definition term229 (x0 : nat) (x1 : nat) := forall y0 : nat, ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 y0))) \/ (Peano.le x1 y0).
Definition term68 := fun y0 : nat => Peano.le y0 y0.
Definition term268 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0.
Definition term263 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0.
Definition term255 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 x1)).
Definition term207 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 \/ (x1 y0).
Definition term257 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) \/ (Peano.lt y0 x0)) x1.
Definition term305 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term248 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term52 := imp (forall y0 : nat, Peano.le y0 y0).
Definition term214 (x0 : nat) (x1 : nat) := @eq Prop (((forall y0 : nat, (~ (Peano.le x1 y0)) \/ (~ (Peano.le y0 x0))) /\ (~ (Peano.lt x0 x1))) \/ (exists y0 : nat, ((Peano.le x1 y0) /\ (Peano.le y0 x0)) /\ (Peano.lt x0 x1))).
Definition term213 (x0 : nat) (x1 : nat) := @eq Prop (((forall y0 : nat, (~ (Peano.le x1 y0)) \/ (~ (Peano.le y0 x0))) /\ (~ (Peano.lt x0 x1))) \/ (exists y0 : nat, (fun y1 : nat => ((Peano.le x1 y1) /\ (Peano.le y1 x0)) /\ (Peano.lt x0 x1)) y0)).
Definition term97 (x0 : nat) := ~ (forall y0 : nat, (forall y1 : nat, ~ ((Peano.le x0 y1) /\ (Peano.le y1 y0))) = (Peano.lt y0 x0)).
Definition term96 (x0 : nat) (x1 : nat) := ~ ((forall y0 : nat, ~ ((Peano.le x1 y0) /\ (Peano.le y0 x0))) = (Peano.lt x0 x1)).
Definition term271 := fun y0 : nat => (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ (forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term47 := ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)).
Definition term41 := ~ (forall y0 : nat, forall y1 : nat, (forall y2 : nat, ~ ((Peano.le y0 y2) /\ (Peano.le y2 y1))) = (Peano.lt y1 y0)).
Definition term95 (x0 : nat) (x1 : nat) := ((forall y0 : nat, (~ (Peano.le x1 y0)) \/ (~ (Peano.le y0 x0))) /\ (~ (Peano.lt x0 x1))) \/ ((exists y0 : nat, (Peano.le x1 y0) /\ (Peano.le y0 x0)) /\ (Peano.lt x0 x1)).
Definition term88 (x0 : nat) (x1 : nat) := and (forall y0 : nat, ~ ((Peano.le x0 y0) /\ (Peano.le y0 x1))).
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term172 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (Peano.le x1 y1) /\ (Peano.le y1 x0)) y0) /\ (Peano.lt x0 x1).
Definition term309 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term21 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (@IN nat y0 x0) = (@IN nat y0 x1).
Definition term338 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term301 (x0 : Prop) := (~ x0) -> x0.
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (~ ((Peano.le x0 x1) /\ (Peano.le x1 x2))).
Definition term187 (x0 : nat) := ((fun y0 : nat => exists y1 : nat, (forall y2 : nat, (~ (Peano.le y0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 y0))) x0) \/ ((fun y0 : nat => exists y1 : nat, exists y2 : nat, ((Peano.le y0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 y0)) x0).
Definition term143 (x0 : nat) := ((fun y0 : nat => exists y1 : nat, (forall y2 : nat, (~ (Peano.le y0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 y0))) x0) \/ ((fun y0 : nat => exists y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 y0)) x0).
Definition term304 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (Peano.le x2 x0)) \/ (~ (Peano.le x1 x2))).
Definition term303 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2))).
Definition term34 (x0 : nat) := forall y0 : nat, (forall y1 : nat, ~ ((Peano.le x0 y1) /\ (Peano.le y1 y0))) = (Peano.lt y0 x0).
Definition term116 (x0 : nat) := fun y0 : nat => (forall y1 : nat, (~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 y0))) /\ (~ (Peano.lt y0 x0)).
Definition term331 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term300 (x0 : nat) := ~ (Peano.le x0 x0).
Definition term138 := fun y0 : nat => exists y1 : nat, (forall y2 : nat, (~ (Peano.le y0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 y0)).
Definition term327 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (Peano.le x1 x0)) \/ ((~ (Peano.le x0 x2)) \/ (Peano.le x1 x2))).
Definition term142 (x0 : nat) := (fun y0 : nat => exists y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 y0)) x0.
Definition term140 (x0 : nat) := (fun y0 : nat => exists y1 : nat, (forall y2 : nat, (~ (Peano.le y0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 y0))) x0.
Definition term321 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> Peano.le x0 x1.
Definition term165 (x0 : nat) (x1 : nat) := and (exists y0 : nat, (fun y1 : nat => (Peano.le x0 y1) /\ (Peano.le y1 x1)) y0).
Definition term252 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0)).
Definition term242 (x0 : nat) := fun y0 : nat => ((~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) /\ ((Peano.le x0 y0) \/ (Peano.lt y0 x0)).
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Peano.le x0 x1) /\ (Peano.le x1 x2)).
Definition term339 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (@IN nat x0 (dotdot x1 x2)).
Definition term283 := @eq Prop (forall y0 : nat, (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ (forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0))).
Definition term282 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0)).
Definition term261 (x0 : nat) := @eq Prop (forall y0 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) /\ ((Peano.le x0 y0) \/ (Peano.lt y0 x0))).
Definition term260 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0) /\ ((fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0)).
Definition term328 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Peano.le x0 x2) \/ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2)))).
Definition term175 (x0 : nat) := fun y0 : nat => exists y1 : nat, ((Peano.le x0 y1) /\ (Peano.le y1 y0)) /\ (Peano.lt y0 x0).
Definition term139 := fun y0 : nat => exists y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 y0).
Definition term210 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.le x1 y0) /\ (Peano.le y0 x0)) /\ (Peano.lt x0 x1)) x2.
Definition term247 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term322 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x2)) \/ (Peano.le x1 x2).
Definition term50 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term162 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1)) x2.
Definition term195 (x0 : nat) := fun y0 : nat => (fun y1 : nat => exists y2 : nat, ((Peano.le x0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 x0)) y0.
Definition term183 := fun y0 : nat => (fun y1 : nat => exists y2 : nat, exists y3 : nat, ((Peano.le y1 y3) /\ (Peano.le y3 y2)) /\ (Peano.lt y2 y1)) y0.
Definition term152 := fun y0 : nat => (fun y1 : nat => exists y2 : nat, (exists y3 : nat, (Peano.le y1 y3) /\ (Peano.le y3 y2)) /\ (Peano.lt y2 y1)) y0.
Definition term147 := fun y0 : nat => (fun y1 : nat => exists y2 : nat, (forall y3 : nat, (~ (Peano.le y1 y3)) \/ (~ (Peano.le y3 y2))) /\ (~ (Peano.lt y2 y1))) y0.
Definition term94 (x0 : nat) (x1 : nat) := ((forall y0 : nat, ~ ((Peano.le x1 y0) /\ (Peano.le y0 x0))) /\ (~ (Peano.lt x0 x1))) \/ ((~ (forall y0 : nat, ~ ((Peano.le x1 y0) /\ (Peano.le y0 x0)))) /\ (Peano.lt x0 x1)).
Definition term299 (x0 : nat) := (~ (Peano.le x0 x0)) -> Peano.le x0 x0.
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term296 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 y1))) \/ (Peano.le x0 y1)) x1.
Definition term9 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (@IN nat y1 (dotdot x0 y0)) = ((Peano.le x0 y1) /\ (Peano.le y1 y0))) x1.
Definition term240 (x0 : nat) (x1 : nat) := ((~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 x1))) /\ ((~ (~ (Peano.le x1 x0))) \/ (Peano.lt x0 x1)).
Definition term276 := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0).
Definition term230 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 y1))) \/ (Peano.le x0 y1).
Definition term64 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term60 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term36 := fun y0 : nat => forall y1 : nat, (forall y2 : nat, ~ ((Peano.le y0 y2) /\ (Peano.le y2 y1))) = (Peano.lt y1 y0).
Definition term35 := fun y0 : nat => forall y1 : nat, ((dotdot y0 y1) = (@EMPTY nat)) = (Peano.lt y1 y0).
Definition term269 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) \/ (Peano.lt y0 x0).
Definition term310 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) -> ~ (Peano.le x1 x2).
Definition term146 := @eq Prop (exists y0 : nat, (exists y1 : nat, (forall y2 : nat, (~ (Peano.le y0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 y0))) \/ (exists y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 y0))).
Definition term145 := @eq Prop (exists y0 : nat, ((fun y1 : nat => exists y2 : nat, (forall y3 : nat, (~ (Peano.le y1 y3)) \/ (~ (Peano.le y3 y2))) /\ (~ (Peano.lt y2 y1))) y0) \/ ((fun y1 : nat => exists y2 : nat, (exists y3 : nat, (Peano.le y1 y3) /\ (Peano.le y3 y2)) /\ (Peano.lt y2 y1)) y0)).
Definition term124 (x0 : nat) := @eq Prop (exists y0 : nat, ((forall y1 : nat, (~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 y0))) /\ (~ (Peano.lt y0 x0))) \/ ((exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) /\ (Peano.lt y0 x0))).
Definition term123 (x0 : nat) := @eq Prop (exists y0 : nat, ((fun y1 : nat => (forall y2 : nat, (~ (Peano.le x0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 x0))) y0) \/ ((fun y1 : nat => (exists y2 : nat, (Peano.le x0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 x0)) y0)).
Definition term208 (x0 : nat) (x1 : nat) := ((forall y0 : nat, (~ (Peano.le x1 y0)) \/ (~ (Peano.le y0 x0))) /\ (~ (Peano.lt x0 x1))) \/ (exists y0 : nat, (fun y1 : nat => ((Peano.le x1 y1) /\ (Peano.le y1 x0)) /\ (Peano.lt x0 x1)) y0).
Definition term237 (x0 : nat) (x1 : nat) := (~ (~ (Peano.le x1 x0))) \/ (Peano.lt x0 x1).
Definition term293 (x0 : nat) := (fun y0 : nat => Peano.le y0 y0) x0.
Definition term57 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term262 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0.
Definition term228 (x0 : nat) (x1 : nat) := fun y0 : nat => ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 y0))) \/ (Peano.le x1 y0).
Definition term236 (x0 : nat) (x1 : nat) := or (Peano.le x0 x1).
Definition term31 (x0 : nat) := fun y0 : nat => ((dotdot x0 y0) = (@EMPTY nat)) = (Peano.lt y0 x0).
Definition term192 (x0 : nat) := (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (~ (Peano.le x0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 x0))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((Peano.le x0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 x0)) y0).
Definition term180 := (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (forall y3 : nat, (~ (Peano.le y1 y3)) \/ (~ (Peano.le y3 y2))) /\ (~ (Peano.lt y2 y1))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, exists y3 : nat, ((Peano.le y1 y3) /\ (Peano.le y3 y2)) /\ (Peano.lt y2 y1)) y0).
Definition term137 := (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (forall y3 : nat, (~ (Peano.le y1 y3)) \/ (~ (Peano.le y3 y2))) /\ (~ (Peano.lt y2 y1))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (exists y3 : nat, (Peano.le y1 y3) /\ (Peano.le y3 y2)) /\ (Peano.lt y2 y1)) y0).
Definition term115 (x0 : nat) := (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (~ (Peano.le x0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 x0))) y0) \/ (exists y0 : nat, (fun y1 : nat => (exists y2 : nat, (Peano.le x0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 x0)) y0).
Definition term46 := (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term61 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term125 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (forall y2 : nat, (~ (Peano.le x0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 x0))) y0.
Definition term127 (x0 : nat) := exists y0 : nat, (forall y1 : nat, (~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 y0))) /\ (~ (Peano.lt y0 x0)).
Definition term45 := (((~ (forall y0 : nat, forall y1 : nat, (forall y2 : nat, ~ ((Peano.le y0 y2) /\ (Peano.le y2 y1))) = (Peano.lt y1 y0))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, (forall y2 : nat, ~ ((Peano.le y0 y2) /\ (Peano.le y2 y1))) = (Peano.lt y1 y0))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> ((~ (forall y0 : nat, forall y1 : nat, (forall y2 : nat, ~ ((Peano.le y0 y2) /\ (Peano.le y2 y1))) = (Peano.lt y1 y0))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, (forall y2 : nat, ~ ((Peano.le y0 y2) /\ (Peano.le y2 y1))) = (Peano.lt y1 y0))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term266 (x0 : nat) := and (forall y0 : nat, (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))).
Definition term89 (x0 : nat) (x1 : nat) := and (forall y0 : nat, (~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 x1))).
Definition term28 (x0 : nat) (x1 : nat) := forall y0 : nat, ~ ((Peano.le x0 y0) /\ (Peano.le y0 x1)).
Definition term43 := ((~ (forall y0 : nat, forall y1 : nat, (forall y2 : nat, ~ ((Peano.le y0 y2) /\ (Peano.le y2 y1))) = (Peano.lt y1 y0))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, (forall y2 : nat, ~ ((Peano.le y0 y2) /\ (Peano.le y2 y1))) = (Peano.lt y1 y0))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term120 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) /\ (Peano.lt y0 x0)) x1.
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term315 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.le x1 x0) \/ (Peano.lt x0 x1)).
Definition term226 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Peano.le x1 x0) /\ (Peano.le x0 x2))) \/ (Peano.le x1 x2).
Definition term205 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term341 (x0 : nat) (x1 : nat) := ((Peano.le x1 x0) /\ (Peano.lt x0 x1)) -> False.
Definition term330 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term194 (x0 : nat) (x1 : nat) := (fun y0 : nat => exists y1 : nat, ((Peano.le x0 y1) /\ (Peano.le y1 y0)) /\ (Peano.lt y0 x0)) x1.
Definition term291 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0).
Definition term286 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0)).
Definition term245 := forall y0 : nat, forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ ((Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term233 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y2))) \/ (Peano.le y0 y2).
Definition term231 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 y1))) \/ (Peano.le x0 y1).
Definition term67 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term65 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term48 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term38 := forall y0 : nat, forall y1 : nat, (forall y2 : nat, ~ ((Peano.le y0 y2) /\ (Peano.le y2 y1))) = (Peano.lt y1 y0).
Definition term37 := forall y0 : nat, forall y1 : nat, ((dotdot y0 y1) = (@EMPTY nat)) = (Peano.lt y1 y0).
Definition term8 (x0 : nat) := forall y0 : nat, forall y1 : nat, (@IN nat y1 (dotdot x0 y0)) = ((Peano.le x0 y1) /\ (Peano.le y1 y0)).
Definition term202 (x0 : nat) := fun y0 : nat => ((forall y1 : nat, (~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 y0))) /\ (~ (Peano.lt y0 x0))) \/ (exists y1 : nat, ((Peano.le x0 y1) /\ (Peano.le y1 y0)) /\ (Peano.lt y0 x0)).
Definition term219 (x0 : nat) (x1 : nat) := exists y0 : nat, ((forall y1 : nat, (~ (Peano.le x1 y1)) \/ (~ (Peano.le y1 x0))) /\ (~ (Peano.lt x0 x1))) \/ (((Peano.le x1 y0) /\ (Peano.le y0 x0)) /\ (Peano.lt x0 x1)).
Definition term103 (x0 : nat) := exists y0 : nat, ((forall y1 : nat, (~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 y0))) /\ (~ (Peano.lt y0 x0))) \/ ((exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) /\ (Peano.lt y0 x0)).
Definition term204 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term319 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) -> False.
Definition term209 (x0 : nat) (x1 : nat) := exists y0 : nat, ((forall y1 : nat, (~ (Peano.le x1 y1)) \/ (~ (Peano.le y1 x0))) /\ (~ (Peano.lt x0 x1))) \/ ((fun y1 : nat => ((Peano.le x1 y1) /\ (Peano.le y1 x0)) /\ (Peano.lt x0 x1)) y0).
Definition term280 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) x0) /\ ((fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)) x0).
Definition term157 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term59 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term44 := (((~ (forall y0 : nat, forall y1 : nat, (forall y2 : nat, ~ ((Peano.le y0 y2) /\ (Peano.le y2 y1))) = (Peano.lt y1 y0))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, (forall y2 : nat, ~ ((Peano.le y0 y2) /\ (Peano.le y2 y1))) = (Peano.lt y1 y0))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, (forall y2 : nat, ~ ((Peano.le y0 y2) /\ (Peano.le y2 y1))) = (Peano.lt y1 y0))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term222 := fun y0 : nat => exists y1 : nat, exists y2 : nat, ((forall y3 : nat, (~ (Peano.le y0 y3)) \/ (~ (Peano.le y3 y1))) /\ (~ (Peano.lt y1 y0))) \/ (((Peano.le y0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 y0)).
Definition term177 := fun y0 : nat => exists y1 : nat, exists y2 : nat, ((Peano.le y0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 y0).
Definition term191 := exists y0 : nat, (exists y1 : nat, (forall y2 : nat, (~ (Peano.le y0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 y0))) \/ (exists y1 : nat, exists y2 : nat, ((Peano.le y0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 y0)).
Definition term135 := exists y0 : nat, (exists y1 : nat, (forall y2 : nat, (~ (Peano.le y0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 y0))) \/ (exists y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 y0)).
Definition term188 (x0 : nat) := (exists y0 : nat, (forall y1 : nat, (~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 y0))) /\ (~ (Peano.lt y0 x0))) \/ (exists y0 : nat, exists y1 : nat, ((Peano.le x0 y1) /\ (Peano.le y1 y0)) /\ (Peano.lt y0 x0)).
Definition term193 (x0 : nat) := exists y0 : nat, ((fun y1 : nat => (forall y2 : nat, (~ (Peano.le x0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 x0))) y0) \/ ((fun y1 : nat => exists y2 : nat, ((Peano.le x0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 x0)) y0).
Definition term181 := exists y0 : nat, ((fun y1 : nat => exists y2 : nat, (forall y3 : nat, (~ (Peano.le y1 y3)) \/ (~ (Peano.le y3 y2))) /\ (~ (Peano.lt y2 y1))) y0) \/ ((fun y1 : nat => exists y2 : nat, exists y3 : nat, ((Peano.le y1 y3) /\ (Peano.le y3 y2)) /\ (Peano.lt y2 y1)) y0).
Definition term136 := exists y0 : nat, ((fun y1 : nat => exists y2 : nat, (forall y3 : nat, (~ (Peano.le y1 y3)) \/ (~ (Peano.le y3 y2))) /\ (~ (Peano.lt y2 y1))) y0) \/ ((fun y1 : nat => exists y2 : nat, (exists y3 : nat, (Peano.le y1 y3) /\ (Peano.le y3 y2)) /\ (Peano.lt y2 y1)) y0).
Definition term114 (x0 : nat) := exists y0 : nat, ((fun y1 : nat => (forall y2 : nat, (~ (Peano.le x0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 x0))) y0) \/ ((fun y1 : nat => (exists y2 : nat, (Peano.le x0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 x0)) y0).
Definition term239 (x0 : nat) (x1 : nat) := and ((~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 x1))).
Definition term218 (x0 : nat) (x1 : nat) := fun y0 : nat => ((forall y1 : nat, (~ (Peano.le x1 y1)) \/ (~ (Peano.le y1 x0))) /\ (~ (Peano.lt x0 x1))) \/ (((Peano.le x1 y0) /\ (Peano.le y0 x0)) /\ (Peano.lt x0 x1)).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term17 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (y0 = y1) = (forall y2 : a0, (@IN a0 y2 y0) = (@IN a0 y2 y1))) x0.
Definition term302 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x2 x0)) \/ (~ (Peano.le x1 x2)).
Definition term10 (x0 : nat) (x1 : nat) := forall y0 : nat, (@IN nat y0 (dotdot x0 x1)) = ((Peano.le x0 y0) /\ (Peano.le y0 x1)).
Definition term151 := or (exists y0 : nat, exists y1 : nat, (forall y2 : nat, (~ (Peano.le y0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 y0))).
Definition term225 (x0 : nat) (x1 : nat) (x2 : nat) := or ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2))).
Definition term159 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) /\ x1.
Definition term40 := (~ (forall y0 : nat, forall y1 : nat, (forall y2 : nat, ~ ((Peano.le y0 y2) /\ (Peano.le y2 y1))) = (Peano.lt y1 y0))) -> False.
Definition term294 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 x1))) x2.
Definition term238 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) \/ (Peano.lt x0 x1).
Definition term107 := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, (forall y3 : nat, ~ ((Peano.le y1 y3) /\ (Peano.le y3 y2))) = (Peano.lt y2 y1)) y0).
Definition term42 := (~ (forall y0 : nat, forall y1 : nat, (forall y2 : nat, ~ ((Peano.le y0 y2) /\ (Peano.le y2 y1))) = (Peano.lt y1 y0))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term258 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) x1) /\ ((fun y0 : nat => (Peano.le x0 y0) \/ (Peano.lt y0 x0)) x1).
Definition term249 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term340 (x0 : nat) (x1 : nat) := ~ ((Peano.le x1 x0) /\ (Peano.lt x0 x1)).
Definition term317 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) -> Peano.lt x0 x1.
Definition term212 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => ((Peano.le x1 y1) /\ (Peano.le y1 x0)) /\ (Peano.lt x0 x1)) y0.
Definition term164 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (Peano.le x0 y1) /\ (Peano.le y1 x1)) y0.
Definition term131 (x0 : nat) := exists y0 : nat, (fun y1 : nat => (exists y2 : nat, (Peano.le x0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 x0)) y0.
Definition term126 (x0 : nat) := exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (~ (Peano.le x0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 x0))) y0.
Definition term199 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (forall y1 : nat, (~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 y0))) /\ (~ (Peano.lt y0 x0))) x1) \/ ((fun y0 : nat => exists y1 : nat, ((Peano.le x0 y1) /\ (Peano.le y1 y0)) /\ (Peano.lt y0 x0)) x1).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term306 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (Peano.le x0 x1))) -> ~ (Peano.le x1 x2).
Definition term337 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Peano.le x0 x1) /\ (Peano.le x1 x2)).
Definition term334 (x0 : nat) (x1 : nat) := and (~ (~ (Peano.le x0 x1))).
Definition term63 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term53 := (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term324 (x0 : nat) (x1 : nat) := or (~ (Peano.le x0 x1)).
Definition term312 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> ~ (Peano.le x0 x1).
Definition term134 := fun y0 : nat => (exists y1 : nat, (forall y2 : nat, (~ (Peano.le y0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 y0))) \/ (exists y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 y0)).
Definition term81 (x0 : nat) (x1 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 x1)).
Definition term270 (x0 : nat) := (forall y0 : nat, (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) /\ (forall y0 : nat, (Peano.le x0 y0) \/ (Peano.lt y0 x0)).
Definition term288 := and (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))).
Definition term201 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (forall y2 : nat, (~ (Peano.le x0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 x0))) y0) \/ ((fun y1 : nat => exists y2 : nat, ((Peano.le x0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 x0)) y0).
Definition term189 := fun y0 : nat => ((fun y1 : nat => exists y2 : nat, (forall y3 : nat, (~ (Peano.le y1 y3)) \/ (~ (Peano.le y3 y2))) /\ (~ (Peano.lt y2 y1))) y0) \/ ((fun y1 : nat => exists y2 : nat, exists y3 : nat, ((Peano.le y1 y3) /\ (Peano.le y3 y2)) /\ (Peano.lt y2 y1)) y0).
Definition term144 := fun y0 : nat => ((fun y1 : nat => exists y2 : nat, (forall y3 : nat, (~ (Peano.le y1 y3)) \/ (~ (Peano.le y3 y2))) /\ (~ (Peano.lt y2 y1))) y0) \/ ((fun y1 : nat => exists y2 : nat, (exists y3 : nat, (Peano.le y1 y3) /\ (Peano.le y3 y2)) /\ (Peano.lt y2 y1)) y0).
Definition term106 (x0 : nat) := ~ ((fun y0 : nat => forall y1 : nat, (forall y2 : nat, ~ ((Peano.le y0 y2) /\ (Peano.le y2 y1))) = (Peano.lt y1 y0)) x0).
Definition term170 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => (Peano.le x2 y0) /\ (Peano.le y0 x1)) x0) /\ (Peano.lt x1 x2).
Definition term83 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term158 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) /\ x1.
Definition term141 (x0 : nat) := or ((fun y0 : nat => exists y1 : nat, (forall y2 : nat, (~ (Peano.le y0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 y0))) x0).
Definition term203 (x0 : nat) := exists y0 : nat, ((forall y1 : nat, (~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 y0))) /\ (~ (Peano.lt y0 x0))) \/ (exists y1 : nat, ((Peano.le x0 y1) /\ (Peano.le y1 y0)) /\ (Peano.lt y0 x0)).
Definition term289 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0.
Definition term284 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0.
Definition term279 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)) x0.
Definition term277 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) x0.
Definition term105 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (forall y2 : nat, ~ ((Peano.le y0 y2) /\ (Peano.le y2 y1))) = (Peano.lt y1 y0)) x0.
Definition term171 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x2 x0) /\ (Peano.le x0 x1)) /\ (Peano.lt x1 x2).
Definition term329 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 x2)))) -> Peano.le x1 x2.
Definition term326 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x2) \/ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2))).
Definition term234 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term217 (x0 : nat) (x1 : nat) := fun y0 : nat => ((forall y1 : nat, (~ (Peano.le x1 y1)) \/ (~ (Peano.le y1 x0))) /\ (~ (Peano.lt x0 x1))) \/ ((fun y1 : nat => ((Peano.le x1 y1) /\ (Peano.le y1 x0)) /\ (Peano.lt x0 x1)) y0).
Definition term85 (x0 : nat) (x1 : nat) := and (exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1)).
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (@IN nat y0 (dotdot x0 x1)) = ((Peano.le x0 y0) /\ (Peano.le y0 x1))) x2.
Definition term227 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 x2))) \/ (Peano.le x1 x2).
Definition term30 (x0 : nat) (x1 : nat) := @eq Prop (forall y0 : nat, ~ ((Peano.le x0 y0) /\ (Peano.le y0 x1))).
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Peano.le x0 x1) /\ (Peano.le x1 x2)).
Definition term253 (x0 : nat) := fun y0 : nat => (Peano.le x0 y0) \/ (Peano.lt y0 x0).
Definition term264 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0)).
Definition term82 (x0 : nat) (x1 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 x1)).
Definition term99 (x0 : nat) (x1 : nat) := (fun y0 : nat => (forall y1 : nat, ~ ((Peano.le x0 y1) /\ (Peano.le y1 y0))) = (Peano.lt y0 x0)) x1.
Definition term332 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2))).
Definition term33 (x0 : nat) := forall y0 : nat, ((dotdot x0 y0) = (@EMPTY nat)) = (Peano.lt y0 x0).
Definition term104 := exists y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, (forall y3 : nat, ~ ((Peano.le y1 y3) /\ (Peano.le y3 y2))) = (Peano.lt y2 y1)) y0).
Definition term98 (x0 : nat) := exists y0 : nat, ~ ((fun y1 : nat => (forall y2 : nat, ~ ((Peano.le x0 y2) /\ (Peano.le y2 y1))) = (Peano.lt y1 x0)) y0).
Definition term75 (x0 : nat) (x1 : nat) := exists y0 : nat, ~ ((fun y1 : nat => ~ ((Peano.le x0 y1) /\ (Peano.le y1 x1))) y0).
Definition term316 (x0 : nat) (x1 : nat) := @eq Prop ((Peano.lt x1 x0) \/ (Peano.le x0 x1)).
Definition term318 (x0 : nat) (x1 : nat) := (~ (Peano.lt x0 x1)) -> Peano.lt x0 x1.
Definition term179 := (exists y0 : nat, exists y1 : nat, (forall y2 : nat, (~ (Peano.le y0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 y0))) \/ (exists y0 : nat, exists y1 : nat, exists y2 : nat, ((Peano.le y0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 y0)).
Definition term155 := (exists y0 : nat, exists y1 : nat, (forall y2 : nat, (~ (Peano.le y0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 y0))) \/ (exists y0 : nat, exists y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 y0)).
Definition term69 := forall y0 : nat, Peano.le y0 y0.
Definition term267 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0.
Definition term51 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)).
Definition term62 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term160 (x0 : nat) (x1 : nat) := (exists y0 : nat, (fun y1 : nat => (Peano.le x1 y1) /\ (Peano.le y1 x0)) y0) /\ (Peano.lt x0 x1).
Definition term87 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.le x1 y0) /\ (Peano.le y0 x0)) /\ (Peano.lt x0 x1).
Definition term287 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0).
Definition term265 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0).
Definition term278 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) x0).
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2)).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ~ ((Peano.le x0 y0) /\ (Peano.le y0 x1))) x2.
Definition term90 (x0 : nat) (x1 : nat) := (forall y0 : nat, ~ ((Peano.le x1 y0) /\ (Peano.le y0 x0))) /\ (~ (Peano.lt x0 x1)).
Definition term132 (x0 : nat) := exists y0 : nat, (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) /\ (Peano.lt y0 x0).
Definition term190 := fun y0 : nat => (exists y1 : nat, (forall y2 : nat, (~ (Peano.le y0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 y0))) \/ (exists y1 : nat, exists y2 : nat, ((Peano.le y0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 y0)).
Definition term84 (x0 : nat) (x1 : nat) := and (~ (forall y0 : nat, ~ ((Peano.le x0 y0) /\ (Peano.le y0 x1)))).
Definition term16 (a0 : Type') (x0 : a0) := (~ (@IN a0 x0 (@EMPTY a0))) -> (@IN a0 x0 (@EMPTY a0)) = False.
Definition term235 (x0 : nat) (x1 : nat) := or (~ (~ (Peano.le x0 x1))).
Definition term215 (x0 : nat) (x1 : nat) (x2 : nat) := ((forall y0 : nat, (~ (Peano.le x1 y0)) \/ (~ (Peano.le y0 x0))) /\ (~ (Peano.lt x0 x1))) \/ ((fun y0 : nat => ((Peano.le x1 y0) /\ (Peano.le y0 x0)) /\ (Peano.lt x0 x1)) x2).
Definition term182 (x0 : nat) := (fun y0 : nat => exists y1 : nat, exists y2 : nat, ((Peano.le y0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 y0)) x0.
Definition term200 (x0 : nat) (x1 : nat) := ((forall y0 : nat, (~ (Peano.le x1 y0)) \/ (~ (Peano.le y0 x0))) /\ (~ (Peano.lt x0 x1))) \/ (exists y0 : nat, ((Peano.le x1 y0) /\ (Peano.le y0 x0)) /\ (Peano.lt x0 x1)).
Definition term79 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term275 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0)).
Definition term54 := (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)).
Definition term27 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ ((Peano.le x0 y0) /\ (Peano.le y0 x1)).
Definition term32 (x0 : nat) := fun y0 : nat => (forall y1 : nat, ~ ((Peano.le x0 y1) /\ (Peano.le y1 y0))) = (Peano.lt y0 x0).
Definition term246 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term196 (x0 : nat) := exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((Peano.le x0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 x0)) y0.
Definition term184 := exists y0 : nat, (fun y1 : nat => exists y2 : nat, exists y3 : nat, ((Peano.le y1 y3) /\ (Peano.le y3 y2)) /\ (Peano.lt y2 y1)) y0.
Definition term153 := exists y0 : nat, (fun y1 : nat => exists y2 : nat, (exists y3 : nat, (Peano.le y1 y3) /\ (Peano.le y3 y2)) /\ (Peano.lt y2 y1)) y0.
Definition term148 := exists y0 : nat, (fun y1 : nat => exists y2 : nat, (forall y3 : nat, (~ (Peano.le y1 y3)) \/ (~ (Peano.le y3 y2))) /\ (~ (Peano.lt y2 y1))) y0.
Definition term223 := exists y0 : nat, exists y1 : nat, exists y2 : nat, ((forall y3 : nat, (~ (Peano.le y0 y3)) \/ (~ (Peano.le y3 y1))) /\ (~ (Peano.lt y1 y0))) \/ (((Peano.le y0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 y0)).
Definition term221 (x0 : nat) := exists y0 : nat, exists y1 : nat, ((forall y2 : nat, (~ (Peano.le x0 y2)) \/ (~ (Peano.le y2 y0))) /\ (~ (Peano.lt y0 x0))) \/ (((Peano.le x0 y1) /\ (Peano.le y1 y0)) /\ (Peano.lt y0 x0)).
Definition term178 := exists y0 : nat, exists y1 : nat, exists y2 : nat, ((Peano.le y0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 y0).
Definition term176 (x0 : nat) := exists y0 : nat, exists y1 : nat, ((Peano.le x0 y1) /\ (Peano.le y1 y0)) /\ (Peano.lt y0 x0).
Definition term154 := exists y0 : nat, exists y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 y0).
Definition term149 := exists y0 : nat, exists y1 : nat, (forall y2 : nat, (~ (Peano.le y0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 y0)).
Definition term109 := exists y0 : nat, exists y1 : nat, ((forall y2 : nat, (~ (Peano.le y0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 y0))) \/ ((exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 y0)).
Definition term272 := forall y0 : nat, (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ (forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term112 (x0 : nat -> Prop) (x1 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ (x1 y0).
Definition term256 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) x1).
Definition term101 (x0 : nat) := fun y0 : nat => ~ ((fun y1 : nat => (forall y2 : nat, ~ ((Peano.le x0 y2) /\ (Peano.le y2 y1))) = (Peano.lt y1 x0)) y0).
Definition term100 (x0 : nat) (x1 : nat) := ~ ((fun y0 : nat => (forall y1 : nat, ~ ((Peano.le x0 y1) /\ (Peano.le y1 y0))) = (Peano.lt y0 x0)) x1).
Definition term241 (x0 : nat) (x1 : nat) := ((~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 x1))) /\ ((Peano.le x1 x0) \/ (Peano.lt x0 x1)).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term325 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x1)) \/ ((Peano.le x0 x2) \/ (~ (Peano.le x1 x2))).
Definition term156 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term311 (x0 : nat) (x1 : nat) := (Peano.le x0 x0) -> ~ (Peano.le x0 x1).
Definition term122 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (forall y2 : nat, (~ (Peano.le x0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 x0))) y0) \/ ((fun y1 : nat => (exists y2 : nat, (Peano.le x0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 x0)) y0).
Definition term86 (x0 : nat) (x1 : nat) := (~ (forall y0 : nat, ~ ((Peano.le x1 y0) /\ (Peano.le y0 x0)))) /\ (Peano.lt x0 x1).
Definition term150 := or (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (forall y3 : nat, (~ (Peano.le y1 y3)) \/ (~ (Peano.le y3 y2))) /\ (~ (Peano.lt y2 y1))) y0).
Definition term128 (x0 : nat) := or (exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (~ (Peano.le x0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 x0))) y0).
Definition term22 (x0 : nat) (x1 : nat) := forall y0 : nat, (@IN nat y0 (dotdot x0 x1)) = (@IN nat y0 (@EMPTY nat)).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (x0 = y0) = (forall y1 : a0, (@IN a0 y1 x0) = (@IN a0 y1 y0))) x1.
Definition term169 (x0 : nat) (x1 : nat) (x2 : nat) := and ((Peano.le x0 x1) /\ (Peano.le x1 x2)).
Definition term29 (x0 : nat) (x1 : nat) := @eq Prop ((dotdot x0 x1) = (@EMPTY nat)).
Definition term121 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (forall y1 : nat, (~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 y0))) /\ (~ (Peano.lt y0 x0))) x1) \/ ((fun y0 : nat => (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) /\ (Peano.lt y0 x0)) x1).
Definition term290 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0.
Definition term285 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0.
Definition term49 := imp (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2).
Definition term102 (x0 : nat) := fun y0 : nat => ((forall y1 : nat, (~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 y0))) /\ (~ (Peano.lt y0 x0))) \/ ((exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) /\ (Peano.lt y0 x0)).
Definition term110 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term73 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term206 (x0 : Prop) (x1 : nat -> Prop) := x0 \/ (exists y0 : nat, x1 y0).
Definition term323 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x2) \/ (~ (Peano.le x1 x2)).
Definition term297 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 y0))) \/ (Peano.le x1 y0)) x2.
Definition term173 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Peano.le x1 y0) /\ (Peano.le y0 x0)) /\ (Peano.lt x0 x1).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (x0 = y0) = (forall y1 : a0, (@IN a0 y1 x0) = (@IN a0 y1 y0)).
Definition term254 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) x1.
Definition term244 := fun y0 : nat => forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ ((Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term335 (x0 : nat) (x1 : nat) := and (Peano.le x0 x1).
Definition term113 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, x1 y0).
Definition term55 := imp (~ (forall y0 : nat, forall y1 : nat, (forall y2 : nat, ~ ((Peano.le y0 y2) /\ (Peano.le y2 y1))) = (Peano.lt y1 y0))).
Definition term313 (x0 : Prop) := x0 -> ~ x0.
Definition term232 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y2))) \/ (Peano.le y0 y2).
Definition term66 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term14 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ (@IN a0 y0 (@EMPTY a0))) x0.
Definition term314 (x0 : nat) (x1 : nat) := (Peano.lt x1 x0) \/ (Peano.le x0 x1).
Definition term308 (x0 : nat) (x1 : nat) := imp (~ (~ (Peano.le x0 x1))).
Definition term211 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => ((Peano.le x1 y1) /\ (Peano.le y1 x0)) /\ (Peano.lt x0 x1)) y0.
Definition term163 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.le x0 y1) /\ (Peano.le y1 x1)) y0.
Definition term130 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (exists y2 : nat, (Peano.le x0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 x0)) y0.
Definition term198 (x0 : nat) := @eq Prop ((exists y0 : nat, (forall y1 : nat, (~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 y0))) /\ (~ (Peano.lt y0 x0))) \/ (exists y0 : nat, exists y1 : nat, ((Peano.le x0 y1) /\ (Peano.le y1 y0)) /\ (Peano.lt y0 x0))).
Definition term197 (x0 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (forall y2 : nat, (~ (Peano.le x0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 x0))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((Peano.le x0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 x0)) y0)).
Definition term186 := @eq Prop ((exists y0 : nat, exists y1 : nat, (forall y2 : nat, (~ (Peano.le y0 y2)) \/ (~ (Peano.le y2 y1))) /\ (~ (Peano.lt y1 y0))) \/ (exists y0 : nat, exists y1 : nat, exists y2 : nat, ((Peano.le y0 y2) /\ (Peano.le y2 y1)) /\ (Peano.lt y1 y0))).
Definition term185 := @eq Prop ((exists y0 : nat, (fun y1 : nat => exists y2 : nat, (forall y3 : nat, (~ (Peano.le y1 y3)) \/ (~ (Peano.le y3 y2))) /\ (~ (Peano.lt y2 y1))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, exists y3 : nat, ((Peano.le y1 y3) /\ (Peano.le y3 y2)) /\ (Peano.lt y2 y1)) y0)).
