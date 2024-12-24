Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term32 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := @eq Prop (forall y0 : a0, (@MEASURE a0 x1 y0 x0) -> @MEASURE a0 x1 y0 x2).
Definition term64 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> nat, forall y2 : a0, (~ ((forall y3 : a0, (Peano.lt (y1 y3) (y1 y2)) -> Peano.lt (y1 y3) (y1 y0)) = (Peano.le (y1 y2) (y1 y0)))) -> (forall y3 : nat, ~ (Peano.lt y3 y3)) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.lt y3 y4) /\ (Peano.le y4 y5)) -> Peano.lt y3 y5) -> ~ (forall y3 : nat, forall y4 : nat, (~ (Peano.le y3 y4)) = (Peano.lt y4 y3)).
Definition term63 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> nat, forall y2 : a0, (~ ((forall y3 : a0, (Peano.lt (y1 y3) (y1 y2)) -> Peano.lt (y1 y3) (y1 y0)) = (Peano.le (y1 y2) (y1 y0)))) -> (forall y3 : nat, ~ (Peano.lt y3 y3)) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.lt y3 y4) /\ (Peano.le y4 y5)) -> Peano.lt y3 y5) -> (forall y3 : nat, forall y4 : nat, (~ (Peano.le y3 y4)) = (Peano.lt y4 y3)) -> False.
Definition term198 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0).
Definition term231 := (~ False) -> False.
Definition term214 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 y0))) \/ (Peano.lt x1 y0)) x2.
Definition term20 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := Peano.lt (x1 x0) (x1 x2).
Definition term40 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := (((~ ((forall y0 : a0, (Peano.lt (x1 y0) (x1 x0)) -> Peano.lt (x1 y0) (x1 x2)) = (Peano.le (x1 x0) (x1 x2)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (~ ((forall y0 : a0, (Peano.lt (x1 y0) (x1 x0)) -> Peano.lt (x1 y0) (x1 x2)) = (Peano.le (x1 x0) (x1 x2)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (~ ((forall y0 : a0, (Peano.lt (x1 y0) (x1 x0)) -> Peano.lt (x1 y0) (x1 x2)) = (Peano.le (x1 x0) (x1 x2)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term140 (x0 : nat) (x1 : nat) (x2 : nat) := or (~ ((Peano.lt x0 x1) /\ (Peano.le x1 x2))).
Definition term144 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x1) /\ (Peano.le x1 x2).
Definition term190 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0).
Definition term167 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0) /\ ((fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0).
Definition term245 (x0 : Prop) := ~ (~ x0).
Definition term212 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y2))) \/ (Peano.lt y0 y2)) x0.
Definition term218 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := ~ (Peano.lt (x0 x1) (x0 x1)).
Definition term84 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := ~ (forall y0 : a0, (Peano.lt (x1 y0) (x1 x0)) -> Peano.lt (x1 y0) (x1 x2)).
Definition term176 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0) /\ ((fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0).
Definition term235 (x0 : nat) (x1 : nat) := or (~ (Peano.lt x0 x1)).
Definition term66 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term12 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := (fun y0 : a0 => (fun y1 : a0 => fun y2 : a0 => Peano.lt (x0 y1) (x0 y2)) y0) x1.
Definition term244 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (Peano.lt x0 x1))) /\ (~ (~ (Peano.le x1 x2))).
Definition term49 := (forall y0 : nat, ~ (Peano.lt y0 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term23 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := @eq Prop ((fun y0 : a0 => Peano.lt (x1 x0) (x1 y0)) x2).
Definition term82 (a0 : Type') (x0 : a0 -> Prop) := ~ (all x0).
Definition term33 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := @eq Prop (forall y0 : a0, (Peano.lt (x1 y0) (x1 x0)) -> Peano.lt (x1 y0) (x1 x2)).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term255 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : a0, (~ ((forall y2 : a0, (Peano.lt (y0 y2) (y0 y1)) -> Peano.lt (y0 y2) (y0 x0)) = (Peano.le (y0 y1) (y0 x0)))) -> (forall y2 : nat, ~ (Peano.lt y2 y2)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.lt y2 y3) /\ (Peano.le y3 y4)) -> Peano.lt y2 y4) -> (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) = (Peano.lt y3 y2)) -> False) x1.
Definition term35 (x0 : Prop) := (~ x0) -> False.
Definition term191 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0).
Definition term168 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0) /\ (forall y0 : nat, (fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0).
Definition term209 := (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ (forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term160 (x0 : nat) := forall y0 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) /\ ((Peano.le x0 y0) \/ (Peano.lt y0 x0)).
Definition term249 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (Peano.lt x0 x1)) \/ (~ (Peano.le x1 x2)))).
Definition term146 (x0 : nat) (x1 : nat) := forall y0 : nat, ((~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 y0))) \/ (Peano.lt x1 y0).
Definition term36 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := (~ ((forall y0 : a0, (Peano.lt (x1 y0) (x1 x0)) -> Peano.lt (x1 y0) (x1 x2)) = (Peano.le (x1 x0) (x1 x2)))) -> False.
Definition term219 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := (Peano.lt (x0 x1) (x0 x1)) -> ~ (Peano.lt (x0 x1) (x0 x1)).
Definition term185 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0.
Definition term180 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0.
Definition term115 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := @eq Prop ((exists y0 : a0, (Peano.lt (x1 y0) (x1 x0)) /\ (~ (Peano.lt (x1 y0) (x1 x2)))) /\ (Peano.le (x1 x0) (x1 x2))).
Definition term114 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := @eq Prop ((exists y0 : a0, (fun y1 : a0 => (Peano.lt (x1 y1) (x1 x0)) /\ (~ (Peano.lt (x1 y1) (x1 x2)))) y0) /\ (Peano.le (x1 x0) (x1 x2))).
Definition term172 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 x1)).
Definition term17 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := (fun y0 : a0 => Peano.lt (x1 x0) (x1 y0)) x2.
Definition term240 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 x2)))) -> Peano.lt x1 x2.
Definition term174 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) \/ (Peano.lt y0 x0)) x1.
Definition term91 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := fun y0 : a0 => (~ (Peano.lt (x1 y0) (x1 x0))) \/ (Peano.lt (x1 y0) (x1 x2)).
Definition term222 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term165 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term62 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> nat, forall y2 : a0, (~ ((forall y3 : a0, (Peano.lt (y1 y3) (y1 y2)) -> Peano.lt (y1 y3) (y1 y0)) = (Peano.le (y1 y2) (y1 y0)))) -> (forall y3 : nat, ~ (Peano.lt y3 y3)) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.lt y3 y4) /\ (Peano.le y4 y5)) -> Peano.lt y3 y5) -> ~ (forall y3 : nat, forall y4 : nat, (~ (Peano.le y3 y4)) = (Peano.lt y4 y3)).
Definition term61 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> nat, forall y2 : a0, (~ ((forall y3 : a0, (Peano.lt (y1 y3) (y1 y2)) -> Peano.lt (y1 y3) (y1 y0)) = (Peano.le (y1 y2) (y1 y0)))) -> (forall y3 : nat, ~ (Peano.lt y3 y3)) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.lt y3 y4) /\ (Peano.le y4 y5)) -> Peano.lt y3 y5) -> (forall y3 : nat, forall y4 : nat, (~ (Peano.le y3 y4)) = (Peano.lt y4 y3)) -> False.
Definition term132 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := @eq Prop (((forall y0 : a0, (~ (Peano.lt (x1 y0) (x1 x0))) \/ (Peano.lt (x1 y0) (x1 x2))) /\ (~ (Peano.le (x1 x0) (x1 x2)))) \/ (exists y0 : a0, ((Peano.lt (x1 y0) (x1 x0)) /\ (~ (Peano.lt (x1 y0) (x1 x2)))) /\ (Peano.le (x1 x0) (x1 x2)))).
Definition term131 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := @eq Prop (((forall y0 : a0, (~ (Peano.lt (x1 y0) (x1 x0))) \/ (Peano.lt (x1 y0) (x1 x2))) /\ (~ (Peano.le (x1 x0) (x1 x2)))) \/ (exists y0 : a0, (fun y1 : a0 => ((Peano.lt (x1 y1) (x1 x0)) /\ (~ (Peano.lt (x1 y1) (x1 x2)))) /\ (Peano.le (x1 x0) (x1 x2))) y0)).
Definition term99 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := and (forall y0 : a0, (~ (Peano.lt (x1 y0) (x1 x0))) \/ (Peano.lt (x1 y0) (x1 x2))).
Definition term98 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := and (forall y0 : a0, (Peano.lt (x1 y0) (x1 x0)) -> Peano.lt (x1 y0) (x1 x2)).
Definition term188 := fun y0 : nat => (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ (forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term87 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) (x3 : a0) := ~ ((fun y0 : a0 => (Peano.lt (x1 y0) (x1 x0)) -> Peano.lt (x1 y0) (x1 x2)) x3).
Definition term43 := ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)).
Definition term26 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) (x3 : a0) := (@MEASURE a0 x1 x2 x0) -> @MEASURE a0 x1 x2 x3.
Definition term251 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> nat) (x3 : a0) := (Peano.lt (x2 x0) (x2 x1)) /\ (Peano.le (x2 x1) (x2 x3)).
Definition term229 (x0 : Prop) := (~ x0) -> x0.
Definition term242 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term238 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (Peano.lt x1 x0)) \/ ((~ (Peano.le x0 x2)) \/ (Peano.lt x1 x2))).
Definition term169 (x0 : nat) := fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0)).
Definition term159 (x0 : nat) := fun y0 : nat => ((~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) /\ ((Peano.le x0 y0) \/ (Peano.lt y0 x0)).
Definition term136 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := fun y0 : a0 => ((forall y1 : a0, (~ (Peano.lt (x1 y1) (x1 x0))) \/ (Peano.lt (x1 y1) (x1 x2))) /\ (~ (Peano.le (x1 x0) (x1 x2)))) \/ (((Peano.lt (x1 y0) (x1 x0)) /\ (~ (Peano.lt (x1 y0) (x1 x2)))) /\ (Peano.le (x1 x0) (x1 x2))).
Definition term200 := @eq Prop (forall y0 : nat, (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ (forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0))).
Definition term199 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0) /\ ((fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0)).
Definition term178 (x0 : nat) := @eq Prop (forall y0 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) /\ ((Peano.le x0 y0) \/ (Peano.lt y0 x0))).
Definition term177 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0) /\ ((fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0)).
Definition term239 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Peano.lt x0 x2) \/ ((~ (Peano.lt x0 x1)) \/ (~ (Peano.le x1 x2)))).
Definition term237 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x2) \/ ((~ (Peano.lt x0 x1)) \/ (~ (Peano.le x1 x2))).
Definition term164 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term46 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term213 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 y1))) \/ (Peano.lt x0 y1)) x1.
Definition term226 (x0 : nat) (x1 : nat) := (~ (Peano.lt x1 x0)) -> Peano.le x0 x1.
Definition term220 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := Peano.lt (x0 x1) (x0 x1).
Definition term157 (x0 : nat) (x1 : nat) := ((~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 x1))) /\ ((~ (~ (Peano.le x1 x0))) \/ (Peano.lt x0 x1)).
Definition term193 := fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0).
Definition term147 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 y1))) \/ (Peano.lt x0 y1).
Definition term72 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.le y0 y1)) -> Peano.lt x0 y1.
Definition term68 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term246 (x0 : nat) (x1 : nat) := ~ (~ (Peano.lt x0 x1)).
Definition term186 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) \/ (Peano.lt y0 x0).
Definition term234 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x2) \/ (~ (Peano.le x1 x2)).
Definition term130 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := exists y0 : a0, (fun y1 : a0 => ((Peano.lt (x1 y1) (x1 x0)) /\ (~ (Peano.lt (x1 y1) (x1 x2)))) /\ (Peano.le (x1 x0) (x1 x2))) y0.
Definition term112 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := exists y0 : a0, (fun y1 : a0 => (Peano.lt (x1 y1) (x1 x0)) /\ (~ (Peano.lt (x1 y1) (x1 x2)))) y0.
Definition term88 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := fun y0 : a0 => ~ ((fun y1 : a0 => (Peano.lt (x1 y1) (x1 x0)) -> Peano.lt (x1 y1) (x1 x2)) y0).
Definition term108 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := (exists y0 : a0, (fun y1 : a0 => (Peano.lt (x1 y1) (x1 x0)) /\ (~ (Peano.lt (x1 y1) (x1 x2)))) y0) /\ (Peano.le (x1 x0) (x1 x2)).
Definition term58 (a0 : Type') (x0 : a0) := fun y0 : a0 -> nat => forall y1 : a0, (~ ((forall y2 : a0, (Peano.lt (y0 y2) (y0 y1)) -> Peano.lt (y0 y2) (y0 x0)) = (Peano.le (y0 y1) (y0 x0)))) -> (forall y2 : nat, ~ (Peano.lt y2 y2)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.lt y2 y3) /\ (Peano.le y3 y4)) -> Peano.lt y2 y4) -> ~ (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) = (Peano.lt y3 y2)).
Definition term57 (a0 : Type') (x0 : a0) := fun y0 : a0 -> nat => forall y1 : a0, (~ ((forall y2 : a0, (Peano.lt (y0 y2) (y0 y1)) -> Peano.lt (y0 y2) (y0 x0)) = (Peano.le (y0 y1) (y0 x0)))) -> (forall y2 : nat, ~ (Peano.lt y2 y2)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.lt y2 y3) /\ (Peano.le y3 y4)) -> Peano.lt y2 y4) -> (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) = (Peano.lt y3 y2)) -> False.
Definition term54 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := fun y0 : a0 => (~ ((forall y1 : a0, (Peano.lt (x0 y1) (x0 y0)) -> Peano.lt (x0 y1) (x0 x1)) = (Peano.le (x0 y0) (x0 x1)))) -> (forall y1 : nat, ~ (Peano.lt y1 y1)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.le y2 y3)) -> Peano.lt y1 y3) -> ~ (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) = (Peano.lt y2 y1)).
Definition term154 (x0 : nat) (x1 : nat) := (~ (~ (Peano.le x1 x0))) \/ (Peano.lt x0 x1).
Definition term105 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := ((forall y0 : a0, (~ (Peano.lt (x1 y0) (x1 x0))) \/ (Peano.lt (x1 y0) (x1 x2))) /\ (~ (Peano.le (x1 x0) (x1 x2)))) \/ ((exists y0 : a0, (Peano.lt (x1 y0) (x1 x0)) /\ (~ (Peano.lt (x1 y0) (x1 x2)))) /\ (Peano.le (x1 x0) (x1 x2))).
Definition term65 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term179 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0.
Definition term153 (x0 : nat) (x1 : nat) := or (Peano.le x0 x1).
Definition term9 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := (fun y0 : a0 => fun y1 : a0 => Peano.lt (x0 y0) (x0 y1)) x1.
Definition term225 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := (Peano.lt (x1 x0) (x1 x2)) -> ~ (Peano.lt (x1 x0) (x1 x2)).
Definition term215 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt x1 x0)) \/ ((~ (Peano.le x0 x2)) \/ (Peano.lt x1 x2)).
Definition term103 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := or ((forall y0 : a0, (~ (Peano.lt (x1 y0) (x1 x0))) \/ (Peano.lt (x1 y0) (x1 x2))) /\ (~ (Peano.le (x1 x0) (x1 x2)))).
Definition term102 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := or ((forall y0 : a0, (Peano.lt (x1 y0) (x1 x0)) -> Peano.lt (x1 y0) (x1 x2)) /\ (~ (Peano.le (x1 x0) (x1 x2)))).
Definition term42 := (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term256 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) (x2 : a0) := (fun y0 : a0 => (~ ((forall y1 : a0, (Peano.lt (x0 y1) (x0 y0)) -> Peano.lt (x0 y1) (x0 x1)) = (Peano.le (x0 y0) (x0 x1)))) -> (forall y1 : nat, ~ (Peano.lt y1 y1)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.le y2 y3)) -> Peano.lt y1 y3) -> (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) = (Peano.lt y2 y1)) -> False) x2.
Definition term134 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> nat) (x3 : a0) := ((forall y0 : a0, (~ (Peano.lt (x2 y0) (x2 x1))) \/ (Peano.lt (x2 y0) (x2 x3))) /\ (~ (Peano.le (x2 x1) (x2 x3)))) \/ (((Peano.lt (x2 x0) (x2 x1)) /\ (~ (Peano.lt (x2 x0) (x2 x3)))) /\ (Peano.le (x2 x1) (x2 x3))).
Definition term28 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := fun y0 : a0 => (@MEASURE a0 x1 y0 x0) -> @MEASURE a0 x1 y0 x2.
Definition term110 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) (x3 : a0) := (fun y0 : a0 => (Peano.lt (x1 y0) (x1 x0)) /\ (~ (Peano.lt (x1 y0) (x1 x2)))) x3.
Definition term122 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := exists y0 : a0, ((Peano.lt (x1 y0) (x1 x0)) /\ (~ (Peano.lt (x1 y0) (x1 x2)))) /\ (Peano.le (x1 x0) (x1 x2)).
Definition term41 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := (((~ ((forall y0 : a0, (Peano.lt (x1 y0) (x1 x0)) -> Peano.lt (x1 y0) (x1 x2)) = (Peano.le (x1 x0) (x1 x2)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (~ ((forall y0 : a0, (Peano.lt (x1 y0) (x1 x0)) -> Peano.lt (x1 y0) (x1 x2)) = (Peano.le (x1 x0) (x1 x2)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> ((~ ((forall y0 : a0, (Peano.lt (x1 y0) (x1 x0)) -> Peano.lt (x1 y0) (x1 x2)) = (Peano.le (x1 x0) (x1 x2)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (~ ((forall y0 : a0, (Peano.lt (x1 y0) (x1 x0)) -> Peano.lt (x1 y0) (x1 x2)) = (Peano.le (x1 x0) (x1 x2)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term183 (x0 : nat) := and (forall y0 : nat, (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))).
Definition term126 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := ((forall y0 : a0, (~ (Peano.lt (x1 y0) (x1 x0))) \/ (Peano.lt (x1 y0) (x1 x2))) /\ (~ (Peano.le (x1 x0) (x1 x2)))) \/ (exists y0 : a0, (fun y1 : a0 => ((Peano.lt (x1 y1) (x1 x0)) /\ (~ (Peano.lt (x1 y1) (x1 x2)))) /\ (Peano.le (x1 x0) (x1 x2))) y0).
Definition term48 := imp (forall y0 : nat, ~ (Peano.lt y0 y0)).
Definition term53 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := fun y0 : a0 => (~ ((forall y1 : a0, (Peano.lt (x0 y1) (x0 y0)) -> Peano.lt (x0 y1) (x0 x1)) = (Peano.le (x0 y0) (x0 x1)))) -> (forall y1 : nat, ~ (Peano.lt y1 y1)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.le y2 y3)) -> Peano.lt y1 y3) -> (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) = (Peano.lt y2 y1)) -> False.
Definition term230 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := (Peano.le (x1 x0) (x1 x2)) -> False.
Definition term111 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := fun y0 : a0 => (fun y1 : a0 => (Peano.lt (x1 y1) (x1 x0)) /\ (~ (Peano.lt (x1 y1) (x1 x2)))) y0.
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term25 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := imp (Peano.lt (x1 x0) (x1 x2)).
Definition term127 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := exists y0 : a0, ((forall y1 : a0, (~ (Peano.lt (x1 y1) (x1 x0))) \/ (Peano.lt (x1 y1) (x1 x2))) /\ (~ (Peano.le (x1 x0) (x1 x2)))) \/ ((fun y1 : a0 => ((Peano.lt (x1 y1) (x1 x0)) /\ (~ (Peano.lt (x1 y1) (x1 x2)))) /\ (Peano.le (x1 x0) (x1 x2))) y0).
Definition term143 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 x2))) \/ (Peano.lt x1 x2).
Definition term125 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := exists y0 : a0, x0 \/ (x1 y0).
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term19 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := (fun y0 : a0 => (fun y1 : a0 => Peano.lt (x1 x0) (x1 y1)) y0) x2.
Definition term241 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term117 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> nat) (x3 : a0) := and ((Peano.lt (x2 x1) (x2 x0)) /\ (~ (Peano.lt (x2 x1) (x2 x3)))).
Definition term83 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0, ~ (x0 y0).
Definition term129 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := fun y0 : a0 => (fun y1 : a0 => ((Peano.lt (x1 y1) (x1 x0)) /\ (~ (Peano.lt (x1 y1) (x1 x2)))) /\ (Peano.le (x1 x0) (x1 x2))) y0.
Definition term208 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0).
Definition term203 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0)).
Definition term162 := forall y0 : nat, forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ ((Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term150 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y2))) \/ (Peano.lt y0 y2).
Definition term148 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((~ (Peano.lt x0 y0)) \/ (~ (Peano.le y0 y1))) \/ (Peano.lt x0 y1).
Definition term75 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2.
Definition term73 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.le y0 y1)) -> Peano.lt x0 y1.
Definition term44 := forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0).
Definition term50 := (forall y0 : nat, ~ (Peano.lt y0 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term11 (a0 : Type') (x0 : type1402 a0) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term124 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 \/ (exists y0 : a0, x1 y0).
Definition term197 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) x0) /\ ((fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)) x0).
Definition term107 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := exists y0 : a0, (x0 y0) /\ x1.
Definition term67 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) = (Peano.lt y0 x0).
Definition term137 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := exists y0 : a0, ((forall y1 : a0, (~ (Peano.lt (x1 y1) (x1 x0))) \/ (Peano.lt (x1 y1) (x1 x2))) /\ (~ (Peano.le (x1 x0) (x1 x2)))) \/ (((Peano.lt (x1 y0) (x1 x0)) /\ (~ (Peano.lt (x1 y0) (x1 x2)))) /\ (Peano.le (x1 x0) (x1 x2))).
Definition term21 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) := fun y0 : a0 => (fun y1 : a0 => Peano.lt (x1 x0) (x1 y1)) y0.
Definition term128 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) (x3 : a0) := (fun y0 : a0 => ((Peano.lt (x1 y0) (x1 x0)) /\ (~ (Peano.lt (x1 y0) (x1 x2)))) /\ (Peano.le (x1 x0) (x1 x2))) x3.
Definition term156 (x0 : nat) (x1 : nat) := and ((~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 x1))).
Definition term95 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := and (exists y0 : a0, (Peano.lt (x1 y0) (x1 x0)) /\ (~ (Peano.lt (x1 y0) (x1 x2)))).
Definition term135 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := fun y0 : a0 => ((forall y1 : a0, (~ (Peano.lt (x1 y1) (x1 x0))) \/ (Peano.lt (x1 y1) (x1 x2))) /\ (~ (Peano.le (x1 x0) (x1 x2)))) \/ ((fun y1 : a0 => ((Peano.lt (x1 y1) (x1 x0)) /\ (~ (Peano.lt (x1 y1) (x1 x2)))) /\ (Peano.le (x1 x0) (x1 x2))) y0).
Definition term24 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) (x2 : a0) := imp (@MEASURE a0 x0 x1 x2).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term145 (x0 : nat) (x1 : nat) := fun y0 : nat => ((~ (Peano.lt x1 x0)) \/ (~ (Peano.le x0 y0))) \/ (Peano.lt x1 y0).
Definition term13 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) := fun y0 : a0 => Peano.lt (x1 x0) (x1 y0).
Definition term76 (x0 : nat) := ~ (Peano.lt x0 x0).
Definition term141 (x0 : nat) (x1 : nat) (x2 : nat) := or ((~ (Peano.lt x0 x1)) \/ (~ (Peano.le x1 x2))).
Definition term22 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := @eq Prop ((fun y0 : a0 => (fun y1 : a0 => Peano.lt (x1 x0) (x1 y1)) y0) x2).
Definition term78 := forall y0 : nat, ~ (Peano.lt y0 y0).
Definition term155 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) \/ (Peano.lt x0 x1).
Definition term211 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) (x3 : a0) := (fun y0 : a0 => (~ (Peano.lt (x1 y0) (x1 x0))) \/ (Peano.lt (x1 y0) (x1 x2))) x3.
Definition term90 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := exists y0 : a0, (Peano.lt (x1 y0) (x1 x0)) /\ (~ (Peano.lt (x1 y0) (x1 x2))).
Definition term97 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := (exists y0 : a0, (Peano.lt (x1 y0) (x1 x0)) /\ (~ (Peano.lt (x1 y0) (x1 x2)))) /\ (Peano.le (x1 x0) (x1 x2)).
Definition term175 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) x1) /\ ((fun y0 : nat => (Peano.le x0 y0) \/ (Peano.lt y0 x0)) x1).
Definition term166 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term116 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) (x3 : a0) := and ((fun y0 : a0 => (Peano.lt (x1 y0) (x1 x0)) /\ (~ (Peano.lt (x1 y0) (x1 x2)))) x3).
Definition term56 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := forall y0 : a0, (~ ((forall y1 : a0, (Peano.lt (x0 y1) (x0 y0)) -> Peano.lt (x0 y1) (x0 x1)) = (Peano.le (x0 y0) (x0 x1)))) -> (forall y1 : nat, ~ (Peano.lt y1 y1)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.le y2 y3)) -> Peano.lt y1 y3) -> ~ (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) = (Peano.lt y2 y1)).
Definition term55 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := forall y0 : a0, (~ ((forall y1 : a0, (Peano.lt (x0 y1) (x0 y0)) -> Peano.lt (x0 y1) (x0 x1)) = (Peano.le (x0 y0) (x0 x1)))) -> (forall y1 : nat, ~ (Peano.lt y1 y1)) -> (forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y1 y2) /\ (Peano.le y2 y3)) -> Peano.lt y1 y3) -> (forall y1 : nat, forall y2 : nat, (~ (Peano.le y1 y2)) = (Peano.lt y2 y1)) -> False.
Definition term16 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := @eq (a0 -> Prop) ((fun y0 : a0 => fun y1 : a0 => Peano.lt (x0 y0) (x0 y1)) x1).
Definition term228 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := (~ (Peano.le (x1 x0) (x1 x2))) -> Peano.le (x1 x0) (x1 x2).
Definition term227 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := (~ (Peano.lt (x1 x2) (x1 x0))) -> Peano.le (x1 x0) (x1 x2).
Definition term96 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := (~ (forall y0 : a0, (Peano.lt (x1 y0) (x1 x0)) -> Peano.lt (x1 y0) (x1 x2))) /\ (Peano.le (x1 x0) (x1 x2)).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term77 := fun y0 : nat => ~ (Peano.lt y0 y0).
Definition term248 (x0 : nat) (x1 : nat) := and (Peano.lt x0 x1).
Definition term250 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Peano.lt x0 x1) /\ (Peano.le x1 x2)).
Definition term247 (x0 : nat) (x1 : nat) := and (~ (~ (Peano.lt x0 x1))).
Definition term101 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := (forall y0 : a0, (~ (Peano.lt (x1 y0) (x1 x0))) \/ (Peano.lt (x1 y0) (x1 x2))) /\ (~ (Peano.le (x1 x0) (x1 x2))).
Definition term100 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := (forall y0 : a0, (Peano.lt (x1 y0) (x1 x0)) -> Peano.lt (x1 y0) (x1 x2)) /\ (~ (Peano.le (x1 x0) (x1 x2))).
Definition term71 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.lt x1 x0) /\ (Peano.le x0 y0)) -> Peano.lt x1 y0.
Definition term217 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := ~ (Peano.lt (x1 x0) (x1 x2)).
Definition term15 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := @eq (a0 -> Prop) ((fun y0 : a0 => (fun y1 : a0 => fun y2 : a0 => Peano.lt (x0 y1) (x0 y2)) y0) x1).
Definition term81 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> nat) (x3 : a0) := (~ (Peano.lt (x2 x1) (x2 x0))) \/ (Peano.lt (x2 x1) (x2 x3)).
Definition term39 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := ((~ ((forall y0 : a0, (Peano.lt (x1 y0) (x1 x0)) -> Peano.lt (x1 y0) (x1 x2)) = (Peano.le (x1 x0) (x1 x2)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False) -> (~ ((forall y0 : a0, (Peano.lt (x1 y0) (x1 x0)) -> Peano.lt (x1 y0) (x1 x2)) = (Peano.le (x1 x0) (x1 x2)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term14 (a0 : Type') (x0 : a0 -> nat) := fun y0 : a0 => (fun y1 : a0 => fun y2 : a0 => Peano.lt (x0 y1) (x0 y2)) y0.
Definition term232 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := (~ (Peano.lt (x1 x0) (x1 x2))) -> Peano.lt (x1 x0) (x1 x2).
Definition term80 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> nat) (x3 : a0) := (Peano.lt (x2 x1) (x2 x0)) /\ (~ (Peano.lt (x2 x1) (x2 x3))).
Definition term30 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := forall y0 : a0, (@MEASURE a0 x1 y0 x0) -> @MEASURE a0 x1 y0 x2.
Definition term187 (x0 : nat) := (forall y0 : nat, (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) /\ (forall y0 : nat, (Peano.le x0 y0) \/ (Peano.lt y0 x0)).
Definition term34 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := Peano.le (x1 x0) (x1 x2).
Definition term205 := and (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))).
Definition term253 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := (Peano.lt (x1 x0) (x1 x2)) -> False.
Definition term27 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> nat) (x3 : a0) := (Peano.lt (x2 x1) (x2 x0)) -> Peano.lt (x2 x1) (x2 x3).
Definition term216 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term206 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0.
Definition term201 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0.
Definition term196 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)) x0.
Definition term194 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) x0.
Definition term92 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := forall y0 : a0, (~ (Peano.lt (x1 y0) (x1 x0))) \/ (Peano.lt (x1 y0) (x1 x2)).
Definition term85 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := exists y0 : a0, ~ ((fun y1 : a0 => (Peano.lt (x1 y1) (x1 x0)) -> Peano.lt (x1 y1) (x1 x2)) y0).
Definition term151 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term51 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := imp (~ ((forall y0 : a0, (Peano.lt (x1 y0) (x1 x0)) -> Peano.lt (x1 y0) (x1 x2)) = (Peano.le (x1 x0) (x1 x2)))).
Definition term79 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> nat) (x3 : a0) := ~ ((Peano.lt (x2 x1) (x2 x0)) -> Peano.lt (x2 x1) (x2 x3)).
Definition term120 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := fun y0 : a0 => ((fun y1 : a0 => (Peano.lt (x1 y1) (x1 x0)) /\ (~ (Peano.lt (x1 y1) (x1 x2)))) y0) /\ (Peano.le (x1 x0) (x1 x2)).
Definition term210 (x0 : nat) := (fun y0 : nat => ~ (Peano.lt y0 y0)) x0.
Definition term138 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Peano.lt x0 x1) /\ (Peano.le x1 x2)).
Definition term170 (x0 : nat) := fun y0 : nat => (Peano.le x0 y0) \/ (Peano.lt y0 x0).
Definition term181 (x0 : nat) := forall y0 : nat, (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0)).
Definition term133 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) (x3 : a0) := ((forall y0 : a0, (~ (Peano.lt (x1 y0) (x1 x0))) \/ (Peano.lt (x1 y0) (x1 x2))) /\ (~ (Peano.le (x1 x0) (x1 x2)))) \/ ((fun y0 : a0 => ((Peano.lt (x1 y0) (x1 x0)) /\ (~ (Peano.lt (x1 y0) (x1 x2)))) /\ (Peano.le (x1 x0) (x1 x2))) x3).
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt x1 x0) /\ (Peano.le x0 x2)) -> Peano.lt x1 x2.
Definition term243 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (Peano.lt x0 x1)) \/ (~ (Peano.le x1 x2))).
Definition term121 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := fun y0 : a0 => ((Peano.lt (x1 y0) (x1 x0)) /\ (~ (Peano.lt (x1 y0) (x1 x2)))) /\ (Peano.le (x1 x0) (x1 x2)).
Definition term223 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> nat) (x3 : a0) := (~ (Peano.lt (x2 x1) (x2 x0))) -> ~ (Peano.lt (x2 x1) (x2 x3)).
Definition term29 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := fun y0 : a0 => (Peano.lt (x1 y0) (x1 x0)) -> Peano.lt (x1 y0) (x1 x2).
Definition term184 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (Peano.le x0 y1) \/ (Peano.lt y1 x0)) y0.
Definition term47 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)).
Definition term252 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> nat) (x3 : a0) := ((Peano.lt (x2 x1) (x2 x0)) /\ (Peano.le (x2 x0) (x2 x3))) -> Peano.lt (x2 x1) (x2 x3).
Definition term204 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0).
Definition term182 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => (~ (Peano.le x0 y1)) \/ (~ (Peano.lt y1 x0))) y0).
Definition term195 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) x0).
Definition term118 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> nat) (x3 : a0) := ((fun y0 : a0 => (Peano.lt (x2 y0) (x2 x1)) /\ (~ (Peano.lt (x2 y0) (x2 x3)))) x0) /\ (Peano.le (x2 x1) (x2 x3)).
Definition term139 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt x0 x1)) \/ (~ (Peano.le x1 x2)).
Definition term104 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := ((forall y0 : a0, (Peano.lt (x1 y0) (x1 x0)) -> Peano.lt (x1 y0) (x1 x2)) /\ (~ (Peano.le (x1 x0) (x1 x2)))) \/ ((~ (forall y0 : a0, (Peano.lt (x1 y0) (x1 x0)) -> Peano.lt (x1 y0) (x1 x2))) /\ (Peano.le (x1 x0) (x1 x2))).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term93 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := ~ (Peano.le (x1 x0) (x1 x2)).
Definition term8 (a0 : Type') (x0 : a0 -> nat) := fun y0 : a0 => fun y1 : a0 => Peano.lt (x0 y0) (x0 y1).
Definition term94 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := and (~ (forall y0 : a0, (Peano.lt (x1 y0) (x1 x0)) -> Peano.lt (x1 y0) (x1 x2))).
Definition term152 (x0 : nat) (x1 : nat) := or (~ (~ (Peano.le x0 x1))).
Definition term37 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := ~ ((forall y0 : a0, (Peano.lt (x1 y0) (x1 x0)) -> Peano.lt (x1 y0) (x1 x2)) = (Peano.le (x1 x0) (x1 x2))).
Definition term192 := fun y0 : nat => forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0)).
Definition term7 (a0 : Type') (x0 : a0 -> nat) := (fun y0 : a0 -> nat => (@MEASURE a0 y0) = (fun y1 : a0 => fun y2 : a0 => Peano.lt (y0 y1) (y0 y2))) x0.
Definition term163 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term189 := forall y0 : nat, (forall y1 : nat, (~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ (forall y1 : nat, (Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term31 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := forall y0 : a0, (Peano.lt (x1 y0) (x1 x0)) -> Peano.lt (x1 y0) (x1 x2).
Definition term173 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) x1).
Definition term158 (x0 : nat) (x1 : nat) := ((~ (Peano.le x1 x0)) \/ (~ (Peano.lt x0 x1))) /\ ((Peano.le x1 x0) \/ (Peano.lt x0 x1)).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term123 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := ((forall y0 : a0, (~ (Peano.lt (x1 y0) (x1 x0))) \/ (Peano.lt (x1 y0) (x1 x2))) /\ (~ (Peano.le (x1 x0) (x1 x2)))) \/ (exists y0 : a0, ((Peano.lt (x1 y0) (x1 x0)) /\ (~ (Peano.lt (x1 y0) (x1 x2)))) /\ (Peano.le (x1 x0) (x1 x2))).
Definition term236 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.lt x0 x1)) \/ ((Peano.lt x0 x2) \/ (~ (Peano.le x1 x2))).
Definition term233 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x2)) \/ (Peano.lt x1 x2).
Definition term106 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (exists y0 : a0, x0 y0) /\ x1.
Definition term113 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := and (exists y0 : a0, (fun y1 : a0 => (Peano.lt (x1 y1) (x1 x0)) /\ (~ (Peano.lt (x1 y1) (x1 x2)))) y0).
Definition term207 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (Peano.le y1 y2) \/ (Peano.lt y2 y1)) y0.
Definition term202 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, (~ (Peano.le y1 y2)) \/ (~ (Peano.lt y2 y1))) y0.
Definition term45 := imp (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2).
Definition term38 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := (~ ((forall y0 : a0, (Peano.lt (x1 y0) (x1 x0)) -> Peano.lt (x1 y0) (x1 x2)) = (Peano.le (x1 x0) (x1 x2)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)) -> False.
Definition term52 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := (~ ((forall y0 : a0, (Peano.lt (x1 y0) (x1 x0)) -> Peano.lt (x1 y0) (x1 x2)) = (Peano.le (x1 x0) (x1 x2)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> ~ (forall y0 : nat, forall y1 : nat, (~ (Peano.le y0 y1)) = (Peano.lt y1 y0)).
Definition term254 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> nat, forall y2 : a0, (~ ((forall y3 : a0, (Peano.lt (y1 y3) (y1 y2)) -> Peano.lt (y1 y3) (y1 y0)) = (Peano.le (y1 y2) (y1 y0)))) -> (forall y3 : nat, ~ (Peano.lt y3 y3)) -> (forall y3 : nat, forall y4 : nat, forall y5 : nat, ((Peano.lt y3 y4) /\ (Peano.le y4 y5)) -> Peano.lt y3 y5) -> (forall y3 : nat, forall y4 : nat, (~ (Peano.le y3 y4)) = (Peano.lt y4 y3)) -> False) x0.
Definition term109 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := exists y0 : a0, ((fun y1 : a0 => (Peano.lt (x1 y1) (x1 x0)) /\ (~ (Peano.lt (x1 y1) (x1 x2)))) y0) /\ (Peano.le (x1 x0) (x1 x2)).
Definition term60 (a0 : Type') (x0 : a0) := forall y0 : a0 -> nat, forall y1 : a0, (~ ((forall y2 : a0, (Peano.lt (y0 y2) (y0 y1)) -> Peano.lt (y0 y2) (y0 x0)) = (Peano.le (y0 y1) (y0 x0)))) -> (forall y2 : nat, ~ (Peano.lt y2 y2)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.lt y2 y3) /\ (Peano.le y3 y4)) -> Peano.lt y2 y4) -> ~ (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) = (Peano.lt y3 y2)).
Definition term59 (a0 : Type') (x0 : a0) := forall y0 : a0 -> nat, forall y1 : a0, (~ ((forall y2 : a0, (Peano.lt (y0 y2) (y0 y1)) -> Peano.lt (y0 y2) (y0 x0)) = (Peano.le (y0 y1) (y0 x0)))) -> (forall y2 : nat, ~ (Peano.lt y2 y2)) -> (forall y2 : nat, forall y3 : nat, forall y4 : nat, ((Peano.lt y2 y3) /\ (Peano.le y3 y4)) -> Peano.lt y2 y4) -> (forall y2 : nat, forall y3 : nat, (~ (Peano.le y2 y3)) = (Peano.lt y3 y2)) -> False.
Definition term86 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) (x3 : a0) := (fun y0 : a0 => (Peano.lt (x1 y0) (x1 x0)) -> Peano.lt (x1 y0) (x1 x2)) x3.
Definition term171 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (Peano.le x0 y0)) \/ (~ (Peano.lt y0 x0))) x1.
Definition term161 := fun y0 : nat => forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.lt y1 y0))) /\ ((Peano.le y0 y1) \/ (Peano.lt y1 y0)).
Definition term142 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Peano.lt x1 x0) /\ (Peano.le x0 x2))) \/ (Peano.lt x1 x2).
Definition term70 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Peano.lt x1 x0) /\ (Peano.le x0 y0)) -> Peano.lt x1 y0.
Definition term89 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := fun y0 : a0 => (Peano.lt (x1 y0) (x1 x0)) /\ (~ (Peano.lt (x1 y0) (x1 x2))).
Definition term221 (x0 : Prop) := x0 -> ~ x0.
Definition term149 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (Peano.lt y0 y1)) \/ (~ (Peano.le y1 y2))) \/ (Peano.lt y0 y2).
Definition term74 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2.
Definition term224 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0) := (~ (Peano.lt (x1 x0) (x1 x0))) -> ~ (Peano.lt (x1 x0) (x1 x2)).
Definition term119 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> nat) (x3 : a0) := ((Peano.lt (x2 x0) (x2 x1)) /\ (~ (Peano.lt (x2 x0) (x2 x3)))) /\ (Peano.le (x2 x1) (x2 x3)).
