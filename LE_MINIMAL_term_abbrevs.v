Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term292 (x0 : nat) := (fun y0 : nat => forall y1 : nat -> Prop, (~ (((y1 (minimal y1)) /\ (forall y2 : nat, (Peano.lt y2 (minimal y1)) -> ~ (y1 y2))) -> (Peano.le y0 (minimal y1)) = (forall y2 : nat, (y1 y2) -> Peano.le y0 y2))) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y2 y3) /\ (Peano.le y3 y4)) -> Peano.le y2 y4) -> (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) = (Peano.lt y3 y2)) -> False) x0.
Definition term21 (x0 : nat -> Prop) (x1 : nat) := (((~ (((x0 (minimal x0)) /\ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0))) -> (Peano.le x1 (minimal x0)) = (forall y0 : nat, (x0 y0) -> Peano.le x1 y0))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (~ (((x0 (minimal x0)) /\ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0))) -> (Peano.le x1 (minimal x0)) = (forall y0 : nat, (x0 y0) -> Peano.le x1 y0))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (~ (((x0 (minimal x0)) /\ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0))) -> (Peano.le x1 (minimal x0)) = (forall y0 : nat, (x0 y0) -> Peano.le x1 y0))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term260 (x0 : nat -> Prop) (x1 : nat) := (~ (Peano.le (minimal x0) x1)) -> Peano.le (minimal x0) x1.
Definition term235 (x0 : nat -> Prop) := and ((@I (nat -> Prop) x0 (minimal x0)) /\ (forall y0 : nat, (~ (Peano.lt y0 (minimal x0))) \/ (~ (@I (nat -> Prop) x0 y0)))).
Definition term202 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0).
Definition term66 (x0 : nat -> Prop) := ~ (all x0).
Definition term282 := (~ False) -> False.
Definition term278 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (Peano.le x0 (minimal x1)) /\ (Peano.le (minimal x1) x2).
Definition term59 (x0 : nat -> Prop) (x1 : nat) := ~ (x0 x1).
Definition term52 (x0 : nat) (x1 : nat -> Prop) := @eq Prop (Peano.le x0 (minimal x1)).
Definition term144 (x0 : nat) (x1 : nat) (x2 : nat) := or (~ ((Peano.le x0 x1) /\ (Peano.le x1 x2))).
Definition term34 (x0 : nat) := forall y0 : nat -> Prop, (~ (((y0 (minimal y0)) /\ (forall y1 : nat, (Peano.lt y1 (minimal y0)) -> ~ (y0 y1))) -> (Peano.le x0 (minimal y0)) = (forall y1 : nat, (y0 y1) -> Peano.le x0 y1))) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y3)) -> Peano.le y1 y3) -> ~ (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) = (Peano.lt y2 y1)).
Definition term232 (x0 : nat -> Prop) := @I (nat -> Prop) x0 (minimal x0).
Definition term194 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0).
Definition term171 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0) /\ ((fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0).
Definition term250 (x0 : Prop) := ~ (~ x0).
Definition term237 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y2))) \/ (Peano.le y0 y2)) x0.
Definition term216 (x0 : nat -> Prop) (x1 : nat) := or (~ (@I (nat -> Prop) x0 x1)).
Definition term56 (x0 : nat -> Prop) := and (x0 (minimal x0)).
Definition term180 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0) /\ ((fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0).
Definition term40 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term242 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x1 x0)) \/ ((~ (Peano.le x0 x2)) \/ (Peano.le x1 x2)).
Definition term287 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := @eq Prop ((Peano.le x0 x2) \/ (~ (@I (nat -> Prop) x1 x2))).
Definition term138 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((x1 (minimal x1)) /\ (forall y0 : nat, (~ (Peano.lt y0 (minimal x1))) \/ (~ (x1 y0)))) /\ (((Peano.le x2 (minimal x1)) /\ ((x1 x0) /\ (~ (Peano.le x2 x0)))) \/ ((~ (Peano.le x2 (minimal x1))) /\ (forall y0 : nat, (~ (x1 y0)) \/ (Peano.le x2 y0)))).
Definition term108 (x0 : nat -> Prop) (x1 : nat) := or (exists y0 : nat, (Peano.le x1 (minimal x0)) /\ ((x0 y0) /\ (~ (Peano.le x1 y0)))).
Definition term273 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (Peano.le x0 x1))) /\ (~ (~ (Peano.le x1 x2))).
Definition term258 (x0 : nat -> Prop) (x1 : nat) := (~ (Peano.lt x1 (minimal x0))) -> Peano.le (minimal x0) x1.
Definition term90 (x0 : nat -> Prop) (x1 : nat) := ((x0 (minimal x0)) /\ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0))) /\ (~ ((Peano.le x1 (minimal x0)) = (forall y0 : nat, (x0 y0) -> Peano.le x1 y0))).
Definition term60 (x0 : nat -> Prop) := fun y0 : nat => (~ (Peano.lt y0 (minimal x0))) \/ (~ (x0 y0)).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term58 (x0 : nat) (x1 : nat -> Prop) := Peano.lt x0 (minimal x1).
Definition term93 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 /\ (x1 y0).
Definition term16 (x0 : Prop) := (~ x0) -> False.
Definition term195 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0).
Definition term172 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0) /\ (forall y0 : nat, (fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0).
Definition term213 := (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term164 (x0 : nat) := forall y0 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) /\ ((Peano.le x0 y0) \/ (Peano.lt y0 x0)).
Definition term110 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) \/ x1.
Definition term276 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2)))).
Definition term150 (x0 : nat) (x1 : nat) := forall y0 : nat, ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 y0))) \/ (Peano.le x1 y0).
Definition term15 (x0 : nat -> Prop) (x1 : nat) := ((x0 (minimal x0)) /\ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0))) -> (Peano.le x1 (minimal x0)) = (forall y0 : nat, (x0 y0) -> Peano.le x1 y0).
Definition term131 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, ((x0 (minimal x0)) /\ (forall y1 : nat, (~ (Peano.lt y1 (minimal x0))) \/ (~ (x0 y1)))) /\ ((fun y1 : nat => ((Peano.le x1 (minimal x0)) /\ ((x0 y1) /\ (~ (Peano.le x1 y1)))) \/ ((~ (Peano.le x1 (minimal x0))) /\ (forall y2 : nat, (~ (x0 y2)) \/ (Peano.le x1 y2)))) y0).
Definition term97 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (Peano.le x1 (minimal x0)) /\ ((fun y1 : nat => (x0 y1) /\ (~ (Peano.le x1 y1))) y0).
Definition term17 (x0 : nat -> Prop) (x1 : nat) := (~ (((x0 (minimal x0)) /\ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0))) -> (Peano.le x1 (minimal x0)) = (forall y0 : nat, (x0 y0) -> Peano.le x1 y0))) -> False.
Definition term103 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (Peano.le x1 (minimal x0)) /\ ((fun y0 : nat => (x0 y0) /\ (~ (Peano.le x1 y0))) x2).
Definition term234 (x0 : nat -> Prop) := (@I (nat -> Prop) x0 (minimal x0)) /\ (forall y0 : nat, (~ (Peano.lt y0 (minimal x0))) \/ (~ (@I (nat -> Prop) x0 y0))).
Definition term50 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (x0 x2) -> Peano.le x1 x2.
Definition term189 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0.
Definition term184 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0.
Definition term176 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 x1)).
Definition term178 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) \/ (Peano.lt y0 x0)) x1.
Definition term247 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term169 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term84 (x0 : nat -> Prop) (x1 : nat) := or ((Peano.le x1 (minimal x0)) /\ (exists y0 : nat, (x0 y0) /\ (~ (Peano.le x1 y0)))).
Definition term283 (x0 : nat -> Prop) := (~ (@I (nat -> Prop) x0 (minimal x0))) -> @I (nat -> Prop) x0 (minimal x0).
Definition term70 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => (x0 y0) -> Peano.le x1 y0) x2.
Definition term68 (x0 : nat -> Prop) (x1 : nat) := ~ (forall y0 : nat, (x0 y0) -> Peano.le x1 y0).
Definition term102 (x0 : nat -> Prop) (x1 : nat) := @eq Prop ((Peano.le x1 (minimal x0)) /\ (exists y0 : nat, (x0 y0) /\ (~ (Peano.le x1 y0)))).
Definition term101 (x0 : nat -> Prop) (x1 : nat) := @eq Prop ((Peano.le x1 (minimal x0)) /\ (exists y0 : nat, (fun y1 : nat => (x0 y1) /\ (~ (Peano.le x1 y1))) y0)).
Definition term192 := fun y0 : nat => (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ (forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term24 := ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)).
Definition term112 (x0 : nat -> Prop) (x1 : Prop) := (exists y0 : nat, x0 y0) \/ x1.
Definition term92 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 /\ (exists y0 : a0, x1 y0).
Definition term218 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (~ (@I (nat -> Prop) x0 y0)) \/ (Peano.le x1 y0).
Definition term53 (x0 : nat -> Prop) (x1 : nat) := (Peano.lt x1 (minimal x0)) -> ~ (x0 x1).
Definition term98 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => (x0 y0) /\ (~ (Peano.le x1 y0))) x2.
Definition term245 (x0 : Prop) := (~ x0) -> x0.
Definition term128 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, ((Peano.le x1 (minimal x0)) /\ ((x0 y0) /\ (~ (Peano.le x1 y0)))) \/ ((~ (Peano.le x1 (minimal x0))) /\ (forall y1 : nat, (~ (x0 y1)) \/ (Peano.le x1 y1))).
Definition term290 (x0 : nat) (x1 : nat -> Prop) := (@I (nat -> Prop) x1 (minimal x1)) -> Peano.le x0 (minimal x1).
Definition term36 := fun y0 : nat => forall y1 : nat -> Prop, (~ (((y1 (minimal y1)) /\ (forall y2 : nat, (Peano.lt y2 (minimal y1)) -> ~ (y1 y2))) -> (Peano.le y0 (minimal y1)) = (forall y2 : nat, (y1 y2) -> Peano.le y0 y2))) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y2 y3) /\ (Peano.le y3 y4)) -> Peano.le y2 y4) -> ~ (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) = (Peano.lt y3 y2)).
Definition term35 := fun y0 : nat => forall y1 : nat -> Prop, (~ (((y1 (minimal y1)) /\ (forall y2 : nat, (Peano.lt y2 (minimal y1)) -> ~ (y1 y2))) -> (Peano.le y0 (minimal y1)) = (forall y2 : nat, (y1 y2) -> Peano.le y0 y2))) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y2 y3) /\ (Peano.le y3 y4)) -> Peano.le y2 y4) -> (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) = (Peano.lt y3 y2)) -> False.
Definition term271 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term267 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (Peano.le x1 x0)) \/ ((~ (Peano.le x0 x2)) \/ (Peano.le x1 x2))).
Definition term280 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) -> Peano.le x0 x1.
Definition term73 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (x0 y0) /\ (~ (Peano.le x1 y0)).
Definition term173 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0)).
Definition term163 (x0 : nat) := fun y0 : nat => ((~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) /\ ((Peano.le x0 y0) \/ (Peano.lt y0 x0)).
Definition term291 (x0 : nat) (x1 : nat -> Prop) := (Peano.le x0 (minimal x1)) -> False.
Definition term204 := @eq Prop (forall y0 : nat, (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ (forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0))).
Definition term203 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0)).
Definition term182 (x0 : nat) := @eq Prop (forall y0 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) /\ ((Peano.le x0 y0) \/ (Peano.lt y0 x0))).
Definition term181 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0) /\ ((fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0)).
Definition term268 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Peano.le x0 x2) \/ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2)))).
Definition term33 (x0 : nat) := forall y0 : nat -> Prop, (~ (((y0 (minimal y0)) /\ (forall y1 : nat, (Peano.lt y1 (minimal y0)) -> ~ (y0 y1))) -> (Peano.le x0 (minimal y0)) = (forall y1 : nat, (y0 y1) -> Peano.le x0 y1))) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y3)) -> Peano.le y1 y3) -> (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) = (Peano.lt y2 y1)) -> False.
Definition term81 (x0 : nat -> Prop) (x1 : nat) := (Peano.le x1 (minimal x0)) /\ (~ (forall y0 : nat, (x0 y0) -> Peano.le x1 y0)).
Definition term226 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((Peano.le x2 (minimal x1)) /\ ((@I (nat -> Prop) x1 x0) /\ (~ (Peano.le x2 x0)))) \/ ((~ (Peano.le x2 (minimal x1))) /\ (forall y0 : nat, (~ (@I (nat -> Prop) x1 y0)) \/ (Peano.le x2 y0))).
Definition term125 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((Peano.le x2 (minimal x1)) /\ ((x1 x0) /\ (~ (Peano.le x2 x0)))) \/ ((~ (Peano.le x2 (minimal x1))) /\ (forall y0 : nat, (~ (x1 y0)) \/ (Peano.le x2 y0))).
Definition term82 (x0 : nat -> Prop) (x1 : nat) := (Peano.le x1 (minimal x0)) /\ (exists y0 : nat, (x0 y0) /\ (~ (Peano.le x1 y0))).
Definition term168 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term262 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x2)) \/ (Peano.le x1 x2).
Definition term217 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (~ (@I (nat -> Prop) x0 x2)) \/ (Peano.le x1 x2).
Definition term106 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (Peano.le x1 (minimal x0)) /\ ((x0 y0) /\ (~ (Peano.le x1 y0))).
Definition term27 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term251 (x0 : nat -> Prop) (x1 : nat) := ~ (~ (@I (nat -> Prop) x0 x1)).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term238 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 y1))) \/ (Peano.le x0 y1)) x1.
Definition term257 (x0 : nat) (x1 : nat) := (~ (Peano.lt x1 x0)) -> Peano.le x0 x1.
Definition term86 (x0 : nat -> Prop) (x1 : nat) := ((Peano.le x1 (minimal x0)) /\ (exists y0 : nat, (x0 y0) /\ (~ (Peano.le x1 y0)))) \/ ((~ (Peano.le x1 (minimal x0))) /\ (forall y0 : nat, (~ (x0 y0)) \/ (Peano.le x1 y0))).
Definition term130 (x0 : nat -> Prop) (x1 : nat) := ((x0 (minimal x0)) /\ (forall y0 : nat, (~ (Peano.lt y0 (minimal x0))) \/ (~ (x0 y0)))) /\ (exists y0 : nat, (fun y1 : nat => ((Peano.le x1 (minimal x0)) /\ ((x0 y1) /\ (~ (Peano.le x1 y1)))) \/ ((~ (Peano.le x1 (minimal x0))) /\ (forall y2 : nat, (~ (x0 y2)) \/ (Peano.le x1 y2)))) y0).
Definition term161 (x0 : nat) (x1 : nat) := ((~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 x1))) /\ ((~ (~ (Peano.le x1 x0))) \/ (Peano.lt x0 x1)).
Definition term197 := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0).
Definition term151 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 y1))) \/ (Peano.le x0 y1).
Definition term46 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term42 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term190 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) \/ (Peano.lt y0 x0).
Definition term19 (x0 : nat -> Prop) (x1 : nat) := (~ (((x0 (minimal x0)) /\ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0))) -> (Peano.le x1 (minimal x0)) = (forall y0 : nat, (x0 y0) -> Peano.le x1 y0))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term126 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (Peano.le x1 (minimal x0)) /\ ((x0 y1) /\ (~ (Peano.le x1 y1)))) y0) \/ ((~ (Peano.le x1 (minimal x0))) /\ (forall y1 : nat, (~ (x0 y1)) \/ (Peano.le x1 y1))).
Definition term95 (x0 : Prop) (x1 : nat -> Prop) := exists y0 : nat, x0 /\ (x1 y0).
Definition term8 (x0 : nat -> Prop) := exists y0 : nat, x0 y0.
Definition term158 (x0 : nat) (x1 : nat) := (~ (~ (Peano.le x1 x0))) \/ (Peano.lt x0 x1).
Definition term140 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => ((x0 (minimal x0)) /\ (forall y1 : nat, (~ (Peano.lt y1 (minimal x0))) \/ (~ (x0 y1)))) /\ (((Peano.le x1 (minimal x0)) /\ ((x0 y0) /\ (~ (Peano.le x1 y0)))) \/ ((~ (Peano.le x1 (minimal x0))) /\ (forall y1 : nat, (~ (x0 y1)) \/ (Peano.le x1 y1)))).
Definition term39 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term183 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0.
Definition term149 (x0 : nat) (x1 : nat) := fun y0 : nat => ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 y0))) \/ (Peano.le x1 y0).
Definition term157 (x0 : nat) (x1 : nat) := or (Peano.le x0 x1).
Definition term228 (x0 : nat -> Prop) (x1 : nat) := (~ (Peano.lt x1 (minimal x0))) \/ (~ (@I (nat -> Prop) x0 x1)).
Definition term94 (x0 : Prop) (x1 : nat -> Prop) := x0 /\ (exists y0 : nat, x1 y0).
Definition term123 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := or ((Peano.le x1 (minimal x0)) /\ ((x0 x2) /\ (~ (Peano.le x1 x2)))).
Definition term115 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, ((fun y1 : nat => (Peano.le x1 (minimal x0)) /\ ((x0 y1) /\ (~ (Peano.le x1 y1)))) y0) \/ ((~ (Peano.le x1 (minimal x0))) /\ (forall y1 : nat, (~ (x0 y1)) \/ (Peano.le x1 y1))).
Definition term23 := (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term43 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term99 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (x0 y1) /\ (~ (Peano.le x1 y1))) y0.
Definition term29 (x0 : nat -> Prop) (x1 : nat) := imp (~ (((x0 (minimal x0)) /\ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0))) -> (Peano.le x1 (minimal x0)) = (forall y0 : nat, (x0 y0) -> Peano.le x1 y0))).
Definition term10 (x0 : nat -> Prop) := imp (exists y0 : nat, x0 y0).
Definition term187 (x0 : nat) := and (forall y0 : nat, (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))).
Definition term31 (x0 : nat) := fun y0 : nat -> Prop => (~ (((y0 (minimal y0)) /\ (forall y1 : nat, (Peano.lt y1 (minimal y0)) -> ~ (y0 y1))) -> (Peano.le x0 (minimal y0)) = (forall y1 : nat, (y0 y1) -> Peano.le x0 y1))) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y3)) -> Peano.le y1 y3) -> (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) = (Peano.lt y2 y1)) -> False.
Definition term224 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (Peano.le x1 (minimal x0)) /\ ((@I (nat -> Prop) x0 x2) /\ (~ (Peano.le x1 x2))).
Definition term284 (x0 : nat -> Prop) := ~ (@I (nat -> Prop) x0 (minimal x0)).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term215 (x0 : nat -> Prop) (x1 : nat) := or (~ (x0 x1)).
Definition term139 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => ((x0 (minimal x0)) /\ (forall y1 : nat, (~ (Peano.lt y1 (minimal x0))) \/ (~ (x0 y1)))) /\ ((fun y1 : nat => ((Peano.le x1 (minimal x0)) /\ ((x0 y1) /\ (~ (Peano.le x1 y1)))) \/ ((~ (Peano.le x1 (minimal x0))) /\ (forall y2 : nat, (~ (x0 y2)) \/ (Peano.le x1 y2)))) y0).
Definition term220 (x0 : nat -> Prop) (x1 : nat) := (~ (Peano.le x1 (minimal x0))) /\ (forall y0 : nat, (~ (@I (nat -> Prop) x0 y0)) \/ (Peano.le x1 y0)).
Definition term79 (x0 : nat -> Prop) (x1 : nat) := (~ (Peano.le x1 (minimal x0))) /\ (forall y0 : nat, (~ (x0 y0)) \/ (Peano.le x1 y0)).
Definition term78 (x0 : nat -> Prop) (x1 : nat) := (~ (Peano.le x1 (minimal x0))) /\ (forall y0 : nat, (x0 y0) -> Peano.le x1 y0).
Definition term146 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Peano.le x1 x0) /\ (Peano.le x0 x2))) \/ (Peano.le x1 x2).
Definition term133 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (fun y1 : nat => ((Peano.le x1 (minimal x0)) /\ ((x0 y1) /\ (~ (Peano.le x1 y1)))) \/ ((~ (Peano.le x1 (minimal x0))) /\ (forall y2 : nat, (~ (x0 y2)) \/ (Peano.le x1 y2)))) y0.
Definition term231 (x0 : nat -> Prop) := x0 (minimal x0).
Definition term270 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term236 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((@I (nat -> Prop) x1 (minimal x1)) /\ (forall y0 : nat, (~ (Peano.lt y0 (minimal x1))) \/ (~ (@I (nat -> Prop) x1 y0)))) /\ (((Peano.le x2 (minimal x1)) /\ ((@I (nat -> Prop) x1 x0) /\ (~ (Peano.le x2 x0)))) \/ ((~ (Peano.le x2 (minimal x1))) /\ (forall y0 : nat, (~ (@I (nat -> Prop) x1 y0)) \/ (Peano.le x2 y0)))).
Definition term212 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0).
Definition term207 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0)).
Definition term166 := forall y0 : nat, forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ ((Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term154 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y2))) \/ (Peano.le y0 y2).
Definition term152 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 y1))) \/ (Peano.le x0 y1).
Definition term49 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term47 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term38 := forall y0 : nat, forall y1 : nat -> Prop, (~ (((y1 (minimal y1)) /\ (forall y2 : nat, (Peano.lt y2 (minimal y1)) -> ~ (y1 y2))) -> (Peano.le y0 (minimal y1)) = (forall y2 : nat, (y1 y2) -> Peano.le y0 y2))) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y2 y3) /\ (Peano.le y3 y4)) -> Peano.le y2 y4) -> ~ (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) = (Peano.lt y3 y2)).
Definition term37 := forall y0 : nat, forall y1 : nat -> Prop, (~ (((y1 (minimal y1)) /\ (forall y2 : nat, (Peano.lt y2 (minimal y1)) -> ~ (y1 y2))) -> (Peano.le y0 (minimal y1)) = (forall y2 : nat, (y1 y2) -> Peano.le y0 y2))) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.le y2 y3) /\ (Peano.le y3 y4)) -> Peano.le y2 y4) -> (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) = (Peano.lt y3 y2)) -> False.
Definition term25 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term13 (x0 : nat -> Prop) (x1 : nat) := forall y0 : nat, (x0 y0) -> Peano.le x1 y0.
Definition term80 (x0 : nat) (x1 : nat -> Prop) := and (Peano.le x0 (minimal x1)).
Definition term71 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ~ ((fun y0 : nat => (x0 y0) -> Peano.le x1 y0) x2).
Definition term233 (x0 : nat -> Prop) := and (@I (nat -> Prop) x0 (minimal x0)).
Definition term201 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) x0) /\ ((fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)) x0).
Definition term253 (x0 : nat -> Prop) (x1 : nat) := imp (@I (nat -> Prop) x0 x1).
Definition term65 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (~ (x0 x2)) \/ (Peano.le x1 x2).
Definition term41 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term20 (x0 : nat -> Prop) (x1 : nat) := ((~ (((x0 (minimal x0)) /\ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0))) -> (Peano.le x1 (minimal x0)) = (forall y0 : nat, (x0 y0) -> Peano.le x1 y0))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (~ (((x0 (minimal x0)) /\ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0))) -> (Peano.le x1 (minimal x0)) = (forall y0 : nat, (x0 y0) -> Peano.le x1 y0))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term249 (x0 : nat) (x1 : nat -> Prop) := ~ (Peano.lt x0 (minimal x1)).
Definition term160 (x0 : nat) (x1 : nat) := and ((~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 x1))).
Definition term74 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (x0 y0) /\ (~ (Peano.le x1 y0)).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term241 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => (~ (@I (nat -> Prop) x0 y0)) \/ (Peano.le x1 y0)) x2.
Definition term111 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) \/ x1.
Definition term51 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (x0 y0) -> Peano.le x1 y0.
Definition term225 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := or ((Peano.le x1 (minimal x0)) /\ ((@I (nat -> Prop) x0 x2) /\ (~ (Peano.le x1 x2)))).
Definition term85 (x0 : nat -> Prop) (x1 : nat) := ((Peano.le x1 (minimal x0)) /\ (~ (forall y0 : nat, (x0 y0) -> Peano.le x1 y0))) \/ ((~ (Peano.le x1 (minimal x0))) /\ (forall y0 : nat, (x0 y0) -> Peano.le x1 y0)).
Definition term145 (x0 : nat) (x1 : nat) (x2 : nat) := or ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2))).
Definition term116 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le x1 (minimal x0)) /\ ((x0 y0) /\ (~ (Peano.le x1 y0)))) x2.
Definition term141 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, ((x0 (minimal x0)) /\ (forall y1 : nat, (~ (Peano.lt y1 (minimal x0))) \/ (~ (x0 y1)))) /\ (((Peano.le x1 (minimal x0)) /\ ((x0 y0) /\ (~ (Peano.le x1 y0)))) \/ ((~ (Peano.le x1 (minimal x0))) /\ (forall y1 : nat, (~ (x0 y1)) \/ (Peano.le x1 y1)))).
Definition term11 (x0 : nat -> Prop) := imp ((x0 (minimal x0)) /\ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0))).
Definition term159 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) \/ (Peano.lt x0 x1).
Definition term227 (x0 : nat) (x1 : nat -> Prop) := or (~ (Peano.lt x0 (minimal x1))).
Definition term179 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) x1) /\ ((fun y0 : nat => (Peano.le x0 y0) \/ (Peano.lt y0 x0)) x1).
Definition term170 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term114 (x0 : nat -> Prop) (x1 : nat) := (exists y0 : nat, (fun y1 : nat => (Peano.le x1 (minimal x0)) /\ ((x0 y1) /\ (~ (Peano.le x1 y1)))) y0) \/ ((~ (Peano.le x1 (minimal x0))) /\ (forall y0 : nat, (~ (x0 y0)) \/ (Peano.le x1 y0))).
Definition term134 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (fun y1 : nat => ((Peano.le x1 (minimal x0)) /\ ((x0 y1) /\ (~ (Peano.le x1 y1)))) \/ ((~ (Peano.le x1 (minimal x0))) /\ (forall y2 : nat, (~ (x0 y2)) \/ (Peano.le x1 y2)))) y0.
Definition term118 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (Peano.le x1 (minimal x0)) /\ ((x0 y1) /\ (~ (Peano.le x1 y1)))) y0.
Definition term100 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (x0 y1) /\ (~ (Peano.le x1 y1))) y0.
Definition term104 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (Peano.le x1 (minimal x0)) /\ ((x0 x2) /\ (~ (Peano.le x1 x2))).
Definition term136 (x0 : nat -> Prop) (x1 : nat) := @eq Prop (((x0 (minimal x0)) /\ (forall y0 : nat, (~ (Peano.lt y0 (minimal x0))) \/ (~ (x0 y0)))) /\ (exists y0 : nat, ((Peano.le x1 (minimal x0)) /\ ((x0 y0) /\ (~ (Peano.le x1 y0)))) \/ ((~ (Peano.le x1 (minimal x0))) /\ (forall y1 : nat, (~ (x0 y1)) \/ (Peano.le x1 y1))))).
Definition term135 (x0 : nat -> Prop) (x1 : nat) := @eq Prop (((x0 (minimal x0)) /\ (forall y0 : nat, (~ (Peano.lt y0 (minimal x0))) \/ (~ (x0 y0)))) /\ (exists y0 : nat, (fun y1 : nat => ((Peano.le x1 (minimal x0)) /\ ((x0 y1) /\ (~ (Peano.le x1 y1)))) \/ ((~ (Peano.le x1 (minimal x0))) /\ (forall y2 : nat, (~ (x0 y2)) \/ (Peano.le x1 y2)))) y0)).
Definition term22 (x0 : nat -> Prop) (x1 : nat) := (((~ (((x0 (minimal x0)) /\ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0))) -> (Peano.le x1 (minimal x0)) = (forall y0 : nat, (x0 y0) -> Peano.le x1 y0))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (~ (((x0 (minimal x0)) /\ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0))) -> (Peano.le x1 (minimal x0)) = (forall y0 : nat, (x0 y0) -> Peano.le x1 y0))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> ((~ (((x0 (minimal x0)) /\ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0))) -> (Peano.le x1 (minimal x0)) = (forall y0 : nat, (x0 y0) -> Peano.le x1 y0))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (~ (((x0 (minimal x0)) /\ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0))) -> (Peano.le x1 (minimal x0)) = (forall y0 : nat, (x0 y0) -> Peano.le x1 y0))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term64 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (x0 x2) /\ (~ (Peano.le x1 x2)).
Definition term223 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (@I (nat -> Prop) x0 x2) /\ (~ (Peano.le x1 x2)).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term277 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Peano.le x0 x1) /\ (Peano.le x1 x2)).
Definition term274 (x0 : nat) (x1 : nat) := and (~ (~ (Peano.le x0 x1))).
Definition term229 (x0 : nat -> Prop) := fun y0 : nat => (~ (Peano.lt y0 (minimal x0))) \/ (~ (@I (nat -> Prop) x0 y0)).
Definition term45 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term109 (x0 : nat -> Prop) (x1 : nat) := (exists y0 : nat, (Peano.le x1 (minimal x0)) /\ ((x0 y0) /\ (~ (Peano.le x1 y0)))) \/ ((~ (Peano.le x1 (minimal x0))) /\ (forall y0 : nat, (~ (x0 y0)) \/ (Peano.le x1 y0))).
Definition term264 (x0 : nat) (x1 : nat) := or (~ (Peano.le x0 x1)).
Definition term87 (x0 : nat -> Prop) (x1 : nat) := ~ ((Peano.le x1 (minimal x0)) = (forall y0 : nat, (x0 y0) -> Peano.le x1 y0)).
Definition term246 (x0 : nat -> Prop) (x1 : nat) := (~ (@I (nat -> Prop) x0 x1)) -> @I (nat -> Prop) x0 x1.
Definition term191 (x0 : nat) := (forall y0 : nat, (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) /\ (forall y0 : nat, (Peano.le x0 y0) \/ (Peano.lt y0 x0)).
Definition term132 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.le x1 (minimal x0)) /\ ((x0 y0) /\ (~ (Peano.le x1 y0)))) \/ ((~ (Peano.le x1 (minimal x0))) /\ (forall y1 : nat, (~ (x0 y1)) \/ (Peano.le x1 y1)))) x2.
Definition term261 (x0 : nat -> Prop) (x1 : nat) := ~ (Peano.le (minimal x0) x1).
Definition term7 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => (exists y1 : nat, y0 y1) = ((y0 (minimal y0)) /\ (forall y1 : nat, (Peano.lt y1 (minimal y0)) -> ~ (y0 y1)))) x0.
Definition term209 := and (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))).
Definition term12 (x0 : nat) (x1 : nat -> Prop) := Peano.le x0 (minimal x1).
Definition term295 := forall y0 : nat -> Prop, forall y1 : nat, (exists y2 : nat, y0 y2) -> (Peano.le y1 (minimal y0)) = (forall y2 : nat, (y0 y2) -> Peano.le y1 y2).
Definition term89 (x0 : nat -> Prop) := and ((x0 (minimal x0)) /\ (forall y0 : nat, (~ (Peano.lt y0 (minimal x0))) \/ (~ (x0 y0)))).
Definition term88 (x0 : nat -> Prop) := and ((x0 (minimal x0)) /\ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0))).
Definition term107 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, (Peano.le x1 (minimal x0)) /\ ((x0 y0) /\ (~ (Peano.le x1 y0))).
Definition term83 (x0 : nat -> Prop) (x1 : nat) := or ((Peano.le x1 (minimal x0)) /\ (~ (forall y0 : nat, (x0 y0) -> Peano.le x1 y0))).
Definition term137 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ((x0 (minimal x0)) /\ (forall y0 : nat, (~ (Peano.lt y0 (minimal x0))) \/ (~ (x0 y0)))) /\ ((fun y0 : nat => ((Peano.le x1 (minimal x0)) /\ ((x0 y0) /\ (~ (Peano.le x1 y0)))) \/ ((~ (Peano.le x1 (minimal x0))) /\ (forall y1 : nat, (~ (x0 y1)) \/ (Peano.le x1 y1)))) x2).
Definition term210 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0.
Definition term205 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0.
Definition term96 (x0 : nat -> Prop) (x1 : nat) := (Peano.le x1 (minimal x0)) /\ (exists y0 : nat, (fun y1 : nat => (x0 y1) /\ (~ (Peano.le x1 y1))) y0).
Definition term286 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := @eq Prop ((~ (@I (nat -> Prop) x0 x2)) \/ (Peano.le x1 x2)).
Definition term200 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)) x0.
Definition term198 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) x0.
Definition term269 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 x2)))) -> Peano.le x1 x2.
Definition term266 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x2) \/ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2))).
Definition term222 (x0 : nat -> Prop) (x1 : nat) := and (@I (nat -> Prop) x0 x1).
Definition term248 (x0 : nat) (x1 : nat -> Prop) := (~ (~ (@I (nat -> Prop) x1 x0))) -> ~ (Peano.lt x0 (minimal x1)).
Definition term155 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term148 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term18 (x0 : nat -> Prop) (x1 : nat) := ~ (((x0 (minimal x0)) /\ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0))) -> (Peano.le x1 (minimal x0)) = (forall y0 : nat, (x0 y0) -> Peano.le x1 y0)).
Definition term259 (x0 : nat -> Prop) (x1 : nat) := Peano.le (minimal x0) x1.
Definition term54 (x0 : nat -> Prop) := fun y0 : nat => (Peano.lt y0 (minimal x0)) -> ~ (x0 y0).
Definition term124 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := ((fun y0 : nat => (Peano.le x2 (minimal x1)) /\ ((x1 y0) /\ (~ (Peano.le x2 y0)))) x0) \/ ((~ (Peano.le x2 (minimal x1))) /\ (forall y0 : nat, (~ (x1 y0)) \/ (Peano.le x2 y0))).
Definition term147 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 x2))) \/ (Peano.le x1 x2).
Definition term142 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Peano.le x0 x1) /\ (Peano.le x1 x2)).
Definition term279 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ((Peano.le x1 (minimal x0)) /\ (Peano.le (minimal x0) x2)) -> Peano.le x1 x2.
Definition term174 (x0 : nat) := fun y0 : nat => (Peano.le x0 y0) \/ (Peano.lt y0 x0).
Definition term230 (x0 : nat -> Prop) := forall y0 : nat, (~ (Peano.lt y0 (minimal x0))) \/ (~ (@I (nat -> Prop) x0 y0)).
Definition term185 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0)).
Definition term121 (x0 : nat -> Prop) (x1 : nat) := @eq Prop ((exists y0 : nat, (Peano.le x1 (minimal x0)) /\ ((x0 y0) /\ (~ (Peano.le x1 y0)))) \/ ((~ (Peano.le x1 (minimal x0))) /\ (forall y0 : nat, (~ (x0 y0)) \/ (Peano.le x1 y0)))).
Definition term120 (x0 : nat -> Prop) (x1 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (Peano.le x1 (minimal x0)) /\ ((x0 y1) /\ (~ (Peano.le x1 y1)))) y0) \/ ((~ (Peano.le x1 (minimal x0))) /\ (forall y0 : nat, (~ (x0 y0)) \/ (Peano.le x1 y0)))).
Definition term272 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2))).
Definition term255 (x0 : nat) (x1 : nat -> Prop) := (Peano.lt x0 (minimal x1)) -> ~ (Peano.lt x0 (minimal x1)).
Definition term32 (x0 : nat) := fun y0 : nat -> Prop => (~ (((y0 (minimal y0)) /\ (forall y1 : nat, (Peano.lt y1 (minimal y0)) -> ~ (y0 y1))) -> (Peano.le x0 (minimal y0)) = (forall y1 : nat, (y0 y1) -> Peano.le x0 y1))) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y3)) -> Peano.le y1 y3) -> ~ (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) = (Peano.lt y2 y1)).
Definition term69 (x0 : nat -> Prop) (x1 : nat) := exists y0 : nat, ~ ((fun y1 : nat => (x0 y1) -> Peano.le x1 y1) y0).
Definition term122 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := or ((fun y0 : nat => (Peano.le x1 (minimal x0)) /\ ((x0 y0) /\ (~ (Peano.le x1 y0)))) x2).
Definition term62 (x0 : nat -> Prop) := (x0 (minimal x0)) /\ (forall y0 : nat, (~ (Peano.lt y0 (minimal x0))) \/ (~ (x0 y0))).
Definition term9 (x0 : nat -> Prop) := (x0 (minimal x0)) /\ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0)).
Definition term188 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0.
Definition term28 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)).
Definition term44 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term117 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.le x1 (minimal x0)) /\ ((x0 y1) /\ (~ (Peano.le x1 y1)))) y0.
Definition term208 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0).
Definition term186 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0).
Definition term199 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) x0).
Definition term143 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2)).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term243 (x0 : nat) (x1 : nat -> Prop) := ~ (Peano.le x0 (minimal x1)).
Definition term289 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (@I (nat -> Prop) x0 x2) -> Peano.le x1 x2.
Definition term294 (x0 : nat -> Prop) := forall y0 : nat, (exists y1 : nat, x0 y1) -> (Peano.le y0 (minimal x0)) = (forall y1 : nat, (x0 y1) -> Peano.le y0 y1).
Definition term156 (x0 : nat) (x1 : nat) := or (~ (~ (Peano.le x0 x1))).
Definition term196 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0)).
Definition term167 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term30 (x0 : nat -> Prop) (x1 : nat) := (~ (((x0 (minimal x0)) /\ (forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0))) -> (Peano.le x1 (minimal x0)) = (forall y0 : nat, (x0 y0) -> Peano.le x1 y0))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)).
Definition term193 := forall y0 : nat, (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ (forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term214 (x0 : nat -> Prop) (x1 : nat) := ~ (@I (nat -> Prop) x0 x1).
Definition term221 (x0 : nat -> Prop) (x1 : nat) := and (x0 x1).
Definition term55 (x0 : nat -> Prop) := forall y0 : nat, (Peano.lt y0 (minimal x0)) -> ~ (x0 y0).
Definition term177 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) x1).
Definition term72 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => ~ ((fun y1 : nat => (x0 y1) -> Peano.le x1 y1) y0).
Definition term57 (x0 : nat -> Prop) (x1 : nat) := (~ (Peano.lt x1 (minimal x0))) \/ (~ (x0 x1)).
Definition term162 (x0 : nat) (x1 : nat) := ((~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 x1))) /\ ((Peano.le x1 x0) \/ (Peano.lt x0 x1)).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term77 (x0 : nat) (x1 : nat -> Prop) := and (~ (Peano.le x0 (minimal x1))).
Definition term265 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x1)) \/ ((Peano.le x0 x2) \/ (~ (Peano.le x1 x2))).
Definition term119 (x0 : nat -> Prop) (x1 : nat) := or (exists y0 : nat, (fun y1 : nat => (Peano.le x1 (minimal x0)) /\ ((x0 y1) /\ (~ (Peano.le x1 y1)))) y0).
Definition term244 (x0 : nat) (x1 : nat -> Prop) := (~ (Peano.le x0 (minimal x1))) -> Peano.le x0 (minimal x1).
Definition term129 (x0 : nat -> Prop) (x1 : nat) := ((x0 (minimal x0)) /\ (forall y0 : nat, (~ (Peano.lt y0 (minimal x0))) \/ (~ (x0 y0)))) /\ (exists y0 : nat, ((Peano.le x1 (minimal x0)) /\ ((x0 y0) /\ (~ (Peano.le x1 y0)))) \/ ((~ (Peano.le x1 (minimal x0))) /\ (forall y1 : nat, (~ (x0 y1)) \/ (Peano.le x1 y1)))).
Definition term219 (x0 : nat -> Prop) (x1 : nat) := forall y0 : nat, (~ (@I (nat -> Prop) x0 y0)) \/ (Peano.le x1 y0).
Definition term76 (x0 : nat -> Prop) (x1 : nat) := forall y0 : nat, (~ (x0 y0)) \/ (Peano.le x1 y0).
Definition term211 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0.
Definition term206 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0.
Definition term26 := imp (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2).
Definition term63 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := ~ ((x0 x2) -> Peano.le x1 x2).
Definition term281 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> False.
Definition term67 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term105 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (Peano.le x1 (minimal x0)) /\ ((fun y1 : nat => (x0 y1) /\ (~ (Peano.le x1 y1))) y0).
Definition term91 (x0 : nat -> Prop) (x1 : nat) := ((x0 (minimal x0)) /\ (forall y0 : nat, (~ (Peano.lt y0 (minimal x0))) \/ (~ (x0 y0)))) /\ (((Peano.le x1 (minimal x0)) /\ (exists y0 : nat, (x0 y0) /\ (~ (Peano.le x1 y0)))) \/ ((~ (Peano.le x1 (minimal x0))) /\ (forall y0 : nat, (~ (x0 y0)) \/ (Peano.le x1 y0)))).
Definition term75 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => (~ (x0 y0)) \/ (Peano.le x1 y0).
Definition term285 (x0 : nat) (x1 : nat -> Prop) (x2 : nat) := (Peano.le x0 x2) \/ (~ (@I (nat -> Prop) x1 x2)).
Definition term263 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x2) \/ (~ (Peano.le x1 x2)).
Definition term254 (x0 : nat) (x1 : nat -> Prop) := (@I (nat -> Prop) x1 x0) -> ~ (Peano.lt x0 (minimal x1)).
Definition term239 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 y0))) \/ (Peano.le x1 y0)) x2.
Definition term14 (x0 : nat -> Prop) (x1 : nat) := (exists y0 : nat, x0 y0) -> (Peano.le x1 (minimal x0)) = (forall y0 : nat, (x0 y0) -> Peano.le x1 y0).
Definition term293 (x0 : nat) (x1 : nat -> Prop) := (fun y0 : nat -> Prop => (~ (((y0 (minimal y0)) /\ (forall y1 : nat, (Peano.lt y1 (minimal y0)) -> ~ (y0 y1))) -> (Peano.le x0 (minimal y0)) = (forall y1 : nat, (y0 y1) -> Peano.le x0 y1))) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y3)) -> Peano.le y1 y3) -> (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) = (Peano.lt y2 y1)) -> False) x1.
Definition term240 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (~ (Peano.lt y0 (minimal x0))) \/ (~ (@I (nat -> Prop) x0 y0))) x1.
Definition term175 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) x1.
Definition term165 := fun y0 : nat => forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ ((Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term275 (x0 : nat) (x1 : nat) := and (Peano.le x0 x1).
Definition term113 (x0 : nat -> Prop) (x1 : Prop) := exists y0 : nat, (x0 y0) \/ x1.
Definition term256 (x0 : Prop) := x0 -> ~ x0.
Definition term153 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y2))) \/ (Peano.le y0 y2).
Definition term48 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term252 (x0 : nat -> Prop) (x1 : nat) := imp (~ (~ (@I (nat -> Prop) x0 x1))).
Definition term61 (x0 : nat -> Prop) := forall y0 : nat, (~ (Peano.lt y0 (minimal x0))) \/ (~ (x0 y0)).
Definition term288 (x0 : nat -> Prop) (x1 : nat) (x2 : nat) := (~ (~ (@I (nat -> Prop) x0 x2))) -> Peano.le x1 x2.
Definition term127 (x0 : nat -> Prop) (x1 : nat) := fun y0 : nat => ((Peano.le x1 (minimal x0)) /\ ((x0 y0) /\ (~ (Peano.le x1 y0)))) \/ ((~ (Peano.le x1 (minimal x0))) /\ (forall y1 : nat, (~ (x0 y1)) \/ (Peano.le x1 y1))).
