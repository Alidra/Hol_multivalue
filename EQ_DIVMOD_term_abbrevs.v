Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term18 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1).
Definition term141 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term225 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x2)) -> (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x2.
Definition term153 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (~ ((Nat.modulo x0 x2) = (Nat.modulo x1 x2))).
Definition term147 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (~ ((Nat.div x0 x2) = (Nat.div x1 x2))).
Definition term40 (x0 : nat -> Prop) := ~ (all x0).
Definition term231 := (~ False) -> False.
Definition term215 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (x0 = x1)) \/ (~ (x0 = x2)))) -> x1 = x2.
Definition term194 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Nat.mul x2 (Nat.div x0 x2)) = (Nat.mul x2 (Nat.div x1 x2))).
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.div x0 x2) = (Nat.div x1 x2)) /\ ((Nat.modulo x0 x2) = (Nat.modulo x1 x2)).
Definition term186 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = x1) /\ (x2 = x3).
Definition term182 (x0 : Prop) := ~ (~ x0).
Definition term57 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) = (y1 = y2)) x0.
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => (((Nat.div x1 x0) = (Nat.div y0 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo y0 x0))) /\ (~ (x1 = y0))) x2) \/ ((fun y0 : nat => ((~ ((Nat.div x1 x0) = (Nat.div y0 x0))) \/ (~ ((Nat.modulo x1 x0) = (Nat.modulo y0 x0)))) /\ (x1 = y0)) x2).
Definition term160 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x3)) \/ ((Nat.add x0 x1) = (Nat.add x2 x3)).
Definition term54 (x0 : nat) := fun y0 : nat => exists y1 : nat, ((((Nat.div y0 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0))) /\ (~ (y0 = y1))) \/ (((~ ((Nat.div y0 x0) = (Nat.div y1 x0))) \/ (~ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0)))) /\ (y0 = y1)).
Definition term181 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (~ (x0 = x1))) /\ (~ (~ (x2 = x3))).
Definition term82 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (((Nat.div x1 x0) = (Nat.div y0 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo y0 x0))) /\ (~ (x1 = y0))).
Definition term218 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x1 = x0))) /\ (~ (~ (x1 = x2))).
Definition term200 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop (((Nat.add x0 x2) = (Nat.add x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term174 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop (((Nat.mul x0 x2) = (Nat.mul x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term191 (x0 : nat) (x1 : nat) (x2 : nat) := ((x2 = x2) /\ ((Nat.div x0 x2) = (Nat.div x1 x2))) -> (Nat.mul x2 (Nat.div x0 x2)) = (Nat.mul x2 (Nat.div x1 x2)).
Definition term86 (x0 : nat) (x1 : nat) := (exists y0 : nat, (((Nat.div x1 x0) = (Nat.div y0 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo y0 x0))) /\ (~ (x1 = y0))) \/ (exists y0 : nat, ((~ ((Nat.div x1 x0) = (Nat.div y0 x0))) \/ (~ ((Nat.modulo x1 x0) = (Nat.modulo y0 x0)))) /\ (x1 = y0)).
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term20 (x0 : nat) := forall y0 : nat, (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)) = x0.
Definition term15 (x0 : nat) := forall y0 : nat, (Nat.add (Nat.mul y0 (Nat.div x0 y0)) (Nat.modulo x0 y0)) = x0.
Definition term165 (x0 : nat) := ~ (x0 = x0).
Definition term31 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.div x0 x2) = (Nat.div x1 x2))) \/ (~ ((Nat.modulo x0 x2) = (Nat.modulo x1 x2))).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term10 := (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0).
Definition term220 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term187 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp (~ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term52 (x0 : nat) (x1 : nat) := ~ ((fun y0 : nat => forall y1 : nat, (((Nat.div y0 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0))) = (y0 = y1)) x1).
Definition term228 (x0 : nat) (x1 : nat) (x2 : nat) := (((Nat.add (Nat.mul x0 (Nat.div x2 x0)) (Nat.modulo x2 x0)) = x1) /\ ((Nat.add (Nat.mul x0 (Nat.div x2 x0)) (Nat.modulo x2 x0)) = x2)) -> x1 = x2.
Definition term26 (x0 : nat) (x1 : nat) := forall y0 : nat, (((Nat.div x1 x0) = (Nat.div y0 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo y0 x0))) = (x1 = y0).
Definition term4 := (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) = (y1 = y2))) -> ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> False.
Definition term227 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add (Nat.mul x1 (Nat.div x2 x1)) (Nat.modulo x2 x1)) = x0) /\ ((Nat.add (Nat.mul x1 (Nat.div x2 x1)) (Nat.modulo x2 x1)) = x2).
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) := ((((Nat.div x1 x0) = (Nat.div x2 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo x2 x0))) /\ (~ (x1 = x2))) \/ ((~ (((Nat.div x1 x0) = (Nat.div x2 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo x2 x0)))) /\ (x1 = x2)).
Definition term206 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Nat.add (Nat.mul x2 (Nat.div x0 x2)) (Nat.modulo x0 x2)) = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2))).
Definition term175 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term185 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term205 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.add (Nat.mul x2 (Nat.div x0 x2)) (Nat.modulo x0 x2)) = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)))) -> (Nat.add (Nat.mul x2 (Nat.div x0 x2)) (Nat.modulo x0 x2)) = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)).
Definition term42 (x0 : nat) (x1 : nat) := ~ (forall y0 : nat, (((Nat.div x1 x0) = (Nat.div y0 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo y0 x0))) = (x1 = y0)).
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) := and ((~ ((Nat.div x0 x2) = (Nat.div x1 x2))) \/ (~ ((Nat.modulo x0 x2) = (Nat.modulo x1 x2)))).
Definition term49 (x0 : nat) := ~ (forall y0 : nat, forall y1 : nat, (((Nat.div y0 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0))) = (y0 = y1)).
Definition term3 := ~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) = (y1 = y2)).
Definition term230 (x0 : nat) (x1 : nat) := (x0 = x1) -> False.
Definition term229 (x0 : nat) (x1 : nat) := (~ (x0 = x1)) -> x0 = x1.
Definition term166 (x0 : Prop) := (~ x0) -> x0.
Definition term219 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = x0) /\ (x1 = x2).
Definition term188 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((x0 = x1) /\ (x2 = x3)).
Definition term118 (x0 : nat) := ((fun y0 : nat => exists y1 : nat, exists y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) /\ (~ (y1 = y2))) x0) \/ ((fun y0 : nat => exists y1 : nat, exists y2 : nat, ((~ ((Nat.div y1 y0) = (Nat.div y2 y0))) \/ (~ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0)))) /\ (y1 = y2)) x0).
Definition term202 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x0 = x2) /\ (x1 = x3)) -> (Nat.add x0 x1) = (Nat.add x2 x3).
Definition term69 (x0 : nat) (x1 : nat) := fun y0 : nat => ((~ ((Nat.div x1 x0) = (Nat.div y0 x0))) \/ (~ ((Nat.modulo x1 x0) = (Nat.modulo y0 x0)))) /\ (x1 = y0).
Definition term167 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.div x0 x2) = (Nat.div x1 x2))) -> (Nat.div x0 x2) = (Nat.div x1 x2).
Definition term216 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ (~ (x1 = x2)).
Definition term179 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term164 (x0 : nat) := (~ (x0 = x0)) -> x0 = x0.
Definition term91 (x0 : nat) := fun y0 : nat => exists y1 : nat, (((Nat.div y0 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0))) /\ (~ (y0 = y1)).
Definition term139 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0) x0.
Definition term213 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2))).
Definition term232 (x0 : nat) (x1 : nat) := (~ ((Nat.div x0 x1) = (Nat.div x0 x1))) -> (Nat.div x0 x1) = (Nat.div x0 x1).
Definition term214 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2)))).
Definition term92 (x0 : nat) := fun y0 : nat => exists y1 : nat, ((~ ((Nat.div y0 x0) = (Nat.div y1 x0))) \/ (~ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0)))) /\ (y0 = y1).
Definition term44 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (((Nat.div x1 x0) = (Nat.div y0 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo y0 x0))) = (x1 = y0)) x2.
Definition term127 := fun y0 : nat => (fun y1 : nat => exists y2 : nat, exists y3 : nat, ((~ ((Nat.div y2 y1) = (Nat.div y3 y1))) \/ (~ ((Nat.modulo y2 y1) = (Nat.modulo y3 y1)))) /\ (y2 = y3)) y0.
Definition term122 := fun y0 : nat => (fun y1 : nat => exists y2 : nat, exists y3 : nat, (((Nat.div y2 y1) = (Nat.div y3 y1)) /\ ((Nat.modulo y2 y1) = (Nat.modulo y3 y1))) /\ (~ (y2 = y3))) y0.
Definition term105 (x0 : nat) := fun y0 : nat => (fun y1 : nat => exists y2 : nat, ((~ ((Nat.div y1 x0) = (Nat.div y2 x0))) \/ (~ ((Nat.modulo y1 x0) = (Nat.modulo y2 x0)))) /\ (y1 = y2)) y0.
Definition term100 (x0 : nat) := fun y0 : nat => (fun y1 : nat => exists y2 : nat, (((Nat.div y1 x0) = (Nat.div y2 x0)) /\ ((Nat.modulo y1 x0) = (Nat.modulo y2 x0))) /\ (~ (y1 = y2))) y0.
Definition term204 (x0 : nat) (x1 : nat) (x2 : nat) := (((Nat.mul x2 (Nat.div x0 x2)) = (Nat.mul x2 (Nat.div x1 x2))) /\ ((Nat.modulo x0 x2) = (Nat.modulo x1 x2))) -> (Nat.add (Nat.mul x2 (Nat.div x0 x2)) (Nat.modulo x0 x2)) = (Nat.add (Nat.mul x2 (Nat.div x1 x2)) (Nat.modulo x1 x2)).
Definition term171 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term51 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (((Nat.div y0 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0))) = (y0 = y1)) x1.
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ ((Nat.div x1 x0) = (Nat.div x2 x0))) \/ (~ ((Nat.modulo x1 x0) = (Nat.modulo x2 x0)))) /\ (x1 = x2).
Definition term198 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.add x0 x2) = (Nat.add x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term172 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.mul x0 x2) = (Nat.mul x1 x3)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term195 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.modulo x0 x2) = (Nat.modulo x1 x2))) -> (Nat.modulo x0 x2) = (Nat.modulo x1 x2).
Definition term27 (x0 : nat) := fun y0 : nat => forall y1 : nat, (((Nat.div y0 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0))) = (y0 = y1).
Definition term196 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.add x0 x2) = (Nat.add x1 x3)) \/ (~ (x2 = x3)).
Definition term168 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.mul x0 x2) = (Nat.mul x1 x3)) \/ (~ (x2 = x3)).
Definition term13 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1).
Definition term121 := @eq Prop (exists y0 : nat, (exists y1 : nat, exists y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) /\ (~ (y1 = y2))) \/ (exists y1 : nat, exists y2 : nat, ((~ ((Nat.div y1 y0) = (Nat.div y2 y0))) \/ (~ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0)))) /\ (y1 = y2))).
Definition term120 := @eq Prop (exists y0 : nat, ((fun y1 : nat => exists y2 : nat, exists y3 : nat, (((Nat.div y2 y1) = (Nat.div y3 y1)) /\ ((Nat.modulo y2 y1) = (Nat.modulo y3 y1))) /\ (~ (y2 = y3))) y0) \/ ((fun y1 : nat => exists y2 : nat, exists y3 : nat, ((~ ((Nat.div y2 y1) = (Nat.div y3 y1))) \/ (~ ((Nat.modulo y2 y1) = (Nat.modulo y3 y1)))) /\ (y2 = y3)) y0)).
Definition term99 (x0 : nat) := @eq Prop (exists y0 : nat, (exists y1 : nat, (((Nat.div y0 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0))) /\ (~ (y0 = y1))) \/ (exists y1 : nat, ((~ ((Nat.div y0 x0) = (Nat.div y1 x0))) \/ (~ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0)))) /\ (y0 = y1))).
Definition term98 (x0 : nat) := @eq Prop (exists y0 : nat, ((fun y1 : nat => exists y2 : nat, (((Nat.div y1 x0) = (Nat.div y2 x0)) /\ ((Nat.modulo y1 x0) = (Nat.modulo y2 x0))) /\ (~ (y1 = y2))) y0) \/ ((fun y1 : nat => exists y2 : nat, ((~ ((Nat.div y1 x0) = (Nat.div y2 x0))) \/ (~ ((Nat.modulo y1 x0) = (Nat.modulo y2 x0)))) /\ (y1 = y2)) y0)).
Definition term77 (x0 : nat) (x1 : nat) := @eq Prop (exists y0 : nat, ((((Nat.div x1 x0) = (Nat.div y0 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo y0 x0))) /\ (~ (x1 = y0))) \/ (((~ ((Nat.div x1 x0) = (Nat.div y0 x0))) \/ (~ ((Nat.modulo x1 x0) = (Nat.modulo y0 x0)))) /\ (x1 = y0))).
Definition term76 (x0 : nat) (x1 : nat) := @eq Prop (exists y0 : nat, ((fun y1 : nat => (((Nat.div x1 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo y1 x0))) /\ (~ (x1 = y1))) y0) \/ ((fun y1 : nat => ((~ ((Nat.div x1 x0) = (Nat.div y1 x0))) \/ (~ ((Nat.modulo x1 x0) = (Nat.modulo y1 x0)))) /\ (x1 = y1)) y0)).
Definition term234 (x0 : nat) (x1 : nat) := (~ ((Nat.modulo x0 x1) = (Nat.modulo x0 x1))) -> (Nat.modulo x0 x1) = (Nat.modulo x0 x1).
Definition term163 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x1)) \/ ((~ (x0 = x2)) \/ (x1 = x2)).
Definition term150 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ ((Nat.modulo y0 x0) = (Nat.modulo x1 x0))) x1.
Definition term144 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ ((Nat.div y0 x0) = (Nat.div x1 x0))) x1.
Definition term212 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term112 := (exists y0 : nat, (fun y1 : nat => exists y2 : nat, exists y3 : nat, (((Nat.div y2 y1) = (Nat.div y3 y1)) /\ ((Nat.modulo y2 y1) = (Nat.modulo y3 y1))) /\ (~ (y2 = y3))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, exists y3 : nat, ((~ ((Nat.div y2 y1) = (Nat.div y3 y1))) \/ (~ ((Nat.modulo y2 y1) = (Nat.modulo y3 y1)))) /\ (y2 = y3)) y0).
Definition term90 (x0 : nat) := (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (((Nat.div y1 x0) = (Nat.div y2 x0)) /\ ((Nat.modulo y1 x0) = (Nat.modulo y2 x0))) /\ (~ (y1 = y2))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((~ ((Nat.div y1 x0) = (Nat.div y2 x0))) \/ (~ ((Nat.modulo y1 x0) = (Nat.modulo y2 x0)))) /\ (y1 = y2)) y0).
Definition term67 (x0 : nat) (x1 : nat) := (exists y0 : nat, (fun y1 : nat => (((Nat.div x1 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo y1 x0))) /\ (~ (x1 = y1))) y0) \/ (exists y0 : nat, (fun y1 : nat => ((~ ((Nat.div x1 x0) = (Nat.div y1 x0))) \/ (~ ((Nat.modulo x1 x0) = (Nat.modulo y1 x0)))) /\ (x1 = y1)) y0).
Definition term78 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (((Nat.div x1 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo y1 x0))) /\ (~ (x1 = y1))) y0.
Definition term138 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Nat.modulo x0 x2) = (Nat.modulo x1 x2)).
Definition term201 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((~ (x0 = x2)) \/ (~ (x1 = x3)))) -> (Nat.add x0 x1) = (Nat.add x2 x3).
Definition term68 (x0 : nat) (x1 : nat) := fun y0 : nat => (((Nat.div x1 x0) = (Nat.div y0 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo y0 x0))) /\ (~ (x1 = y0)).
Definition term32 (x0 : nat) (x1 : nat) (x2 : nat) := and (~ (((Nat.div x0 x2) = (Nat.div x1 x2)) /\ ((Nat.modulo x0 x2) = (Nat.modulo x1 x2)))).
Definition term94 (x0 : nat) (x1 : nat) := or ((fun y0 : nat => exists y1 : nat, (((Nat.div y0 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0))) /\ (~ (y0 = y1))) x1).
Definition term178 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term95 (x0 : nat) (x1 : nat) := (fun y0 : nat => exists y1 : nat, ((~ ((Nat.div y0 x0) = (Nat.div y1 x0))) \/ (~ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0)))) /\ (y0 = y1)) x1.
Definition term93 (x0 : nat) (x1 : nat) := (fun y0 : nat => exists y1 : nat, (((Nat.div y0 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0))) /\ (~ (y0 = y1))) x1.
Definition term28 (x0 : nat) := forall y0 : nat, forall y1 : nat, (((Nat.div y0 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0))) = (y0 = y1).
Definition term22 := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0.
Definition term17 := forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0.
Definition term1 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) = (y1 = y2).
Definition term48 (x0 : nat) (x1 : nat) := exists y0 : nat, ((((Nat.div x1 x0) = (Nat.div y0 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo y0 x0))) /\ (~ (x1 = y0))) \/ (((~ ((Nat.div x1 x0) = (Nat.div y0 x0))) \/ (~ ((Nat.modulo x1 x0) = (Nat.modulo y0 x0)))) /\ (x1 = y0)).
Definition term148 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ ((Nat.modulo y0 x1) = (Nat.modulo x0 x1)).
Definition term142 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ ((Nat.div y0 x1) = (Nat.div x0 x1)).
Definition term45 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((fun y0 : nat => (((Nat.div x1 x0) = (Nat.div y0 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo y0 x0))) = (x1 = y0)) x2).
Definition term207 (x0 : nat) (x1 : nat) := (~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1)) -> (Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1.
Definition term14 (x0 : nat) := fun y0 : nat => (Nat.add (Nat.mul y0 (Nat.div x0 y0)) (Nat.modulo x0 y0)) = x0.
Definition term114 := fun y0 : nat => exists y1 : nat, exists y2 : nat, ((~ ((Nat.div y1 y0) = (Nat.div y2 y0))) \/ (~ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0)))) /\ (y1 = y2).
Definition term113 := fun y0 : nat => exists y1 : nat, exists y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) /\ (~ (y1 = y2)).
Definition term60 := fun y0 : nat => exists y1 : nat, exists y2 : nat, ((((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) /\ (~ (y1 = y2))) \/ (((~ ((Nat.div y1 y0) = (Nat.div y2 y0))) \/ (~ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0)))) /\ (y1 = y2)).
Definition term199 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((Nat.add x0 x1) = (Nat.add x2 x3)))).
Definition term173 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((Nat.mul x0 x1) = (Nat.mul x2 x3)))).
Definition term110 := exists y0 : nat, (exists y1 : nat, exists y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) /\ (~ (y1 = y2))) \/ (exists y1 : nat, exists y2 : nat, ((~ ((Nat.div y1 y0) = (Nat.div y2 y0))) \/ (~ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0)))) /\ (y1 = y2)).
Definition term88 (x0 : nat) := exists y0 : nat, (exists y1 : nat, (((Nat.div y0 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0))) /\ (~ (y0 = y1))) \/ (exists y1 : nat, ((~ ((Nat.div y0 x0) = (Nat.div y1 x0))) \/ (~ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0)))) /\ (y0 = y1)).
Definition term47 (x0 : nat) (x1 : nat) := fun y0 : nat => ((((Nat.div x1 x0) = (Nat.div y0 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo y0 x0))) /\ (~ (x1 = y0))) \/ (((~ ((Nat.div x1 x0) = (Nat.div y0 x0))) \/ (~ ((Nat.modulo x1 x0) = (Nat.modulo y0 x0)))) /\ (x1 = y0)).
Definition term111 := exists y0 : nat, ((fun y1 : nat => exists y2 : nat, exists y3 : nat, (((Nat.div y2 y1) = (Nat.div y3 y1)) /\ ((Nat.modulo y2 y1) = (Nat.modulo y3 y1))) /\ (~ (y2 = y3))) y0) \/ ((fun y1 : nat => exists y2 : nat, exists y3 : nat, ((~ ((Nat.div y2 y1) = (Nat.div y3 y1))) \/ (~ ((Nat.modulo y2 y1) = (Nat.modulo y3 y1)))) /\ (y2 = y3)) y0).
Definition term89 (x0 : nat) := exists y0 : nat, ((fun y1 : nat => exists y2 : nat, (((Nat.div y1 x0) = (Nat.div y2 x0)) /\ ((Nat.modulo y1 x0) = (Nat.modulo y2 x0))) /\ (~ (y1 = y2))) y0) \/ ((fun y1 : nat => exists y2 : nat, ((~ ((Nat.div y1 x0) = (Nat.div y2 x0))) \/ (~ ((Nat.modulo y1 x0) = (Nat.modulo y2 x0)))) /\ (y1 = y2)) y0).
Definition term66 (x0 : nat) (x1 : nat) := exists y0 : nat, ((fun y1 : nat => (((Nat.div x1 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo y1 x0))) /\ (~ (x1 = y1))) y0) \/ ((fun y1 : nat => ((~ ((Nat.div x1 x0) = (Nat.div y1 x0))) \/ (~ ((Nat.modulo x1 x0) = (Nat.modulo y1 x0)))) /\ (x1 = y1)) y0).
Definition term73 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((~ ((Nat.div x1 x0) = (Nat.div y0 x0))) \/ (~ ((Nat.modulo x1 x0) = (Nat.modulo y0 x0)))) /\ (x1 = y0)) x2.
Definition term203 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.mul x2 (Nat.div x0 x2)) = (Nat.mul x2 (Nat.div x1 x2))) /\ ((Nat.modulo x0 x2) = (Nat.modulo x1 x2)).
Definition term159 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x1 = x3) -> (Nat.add x0 x1) = (Nat.add x2 x3).
Definition term154 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x1 = x3) -> (Nat.mul x0 x1) = (Nat.mul x2 x3).
Definition term226 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x2).
Definition term210 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = x2) \/ (~ (x1 = x2)).
Definition term96 (x0 : nat) (x1 : nat) := ((fun y0 : nat => exists y1 : nat, (((Nat.div y0 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0))) /\ (~ (y0 = y1))) x1) \/ ((fun y0 : nat => exists y1 : nat, ((~ ((Nat.div y0 x0) = (Nat.div y1 x0))) \/ (~ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0)))) /\ (y0 = y1)) x1).
Definition term126 := or (exists y0 : nat, exists y1 : nat, exists y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) /\ (~ (y1 = y2))).
Definition term104 (x0 : nat) := or (exists y0 : nat, exists y1 : nat, (((Nat.div y0 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0))) /\ (~ (y0 = y1))).
Definition term85 (x0 : nat) (x1 : nat) := exists y0 : nat, ((~ ((Nat.div x1 x0) = (Nat.div y0 x0))) \/ (~ ((Nat.modulo x1 x0) = (Nat.modulo y0 x0)))) /\ (x1 = y0).
Definition term2 := (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) = (y1 = y2))) -> False.
Definition term59 := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, forall y3 : nat, (((Nat.div y2 y1) = (Nat.div y3 y1)) /\ ((Nat.modulo y2 y1) = (Nat.modulo y3 y1))) = (y2 = y3)) y0).
Definition term53 (x0 : nat) := fun y0 : nat => ~ ((fun y1 : nat => forall y2 : nat, (((Nat.div y1 x0) = (Nat.div y2 x0)) /\ ((Nat.modulo y1 x0) = (Nat.modulo y2 x0))) = (y1 = y2)) y0).
Definition term189 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x0 = x2) /\ (x1 = x3)) -> (Nat.mul x0 x1) = (Nat.mul x2 x3).
Definition term192 (x0 : nat) (x1 : nat) := Nat.mul x1 (Nat.div x0 x1).
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat) := ~ (((Nat.div x0 x2) = (Nat.div x1 x2)) /\ ((Nat.modulo x0 x2) = (Nat.modulo x1 x2))).
Definition term224 (x0 : nat) (x1 : nat) (x2 : nat) := (((Nat.add (Nat.mul x1 (Nat.div x2 x1)) (Nat.modulo x2 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) /\ ((Nat.add (Nat.mul x1 (Nat.div x2 x1)) (Nat.modulo x2 x1)) = x2)) -> (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1)) = x2.
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (((Nat.div x1 x0) = (Nat.div y0 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo y0 x0))) /\ (~ (x1 = y0))) x2.
Definition term211 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x1 = x0)) \/ ((x0 = x2) \/ (~ (x1 = x2))).
Definition term84 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => ((~ ((Nat.div x1 x0) = (Nat.div y1 x0))) \/ (~ ((Nat.modulo x1 x0) = (Nat.modulo y1 x0)))) /\ (x1 = y1)) y0.
Definition term79 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (((Nat.div x1 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo y1 x0))) /\ (~ (x1 = y1))) y0.
Definition term190 (x0 : nat) (x1 : nat) (x2 : nat) := (x2 = x2) /\ ((Nat.div x0 x2) = (Nat.div x1 x2)).
Definition term9 := ~ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)).
Definition term184 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term25 (x0 : nat) (x1 : nat) := fun y0 : nat => (((Nat.div x1 x0) = (Nat.div y0 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo y0 x0))) = (x1 = y0).
Definition term152 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : nat => ~ ((Nat.modulo y0 x1) = (Nat.modulo x0 x1))) x2).
Definition term146 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : nat => ~ ((Nat.div y0 x1) = (Nat.div x0 x1))) x2).
Definition term87 (x0 : nat) := fun y0 : nat => (exists y1 : nat, (((Nat.div y0 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0))) /\ (~ (y0 = y1))) \/ (exists y1 : nat, ((~ ((Nat.div y0 x0) = (Nat.div y1 x0))) \/ (~ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0)))) /\ (y0 = y1)).
Definition term151 (x0 : nat) (x1 : nat) := ~ ((Nat.modulo x0 x1) = (Nat.modulo x0 x1)).
Definition term235 (x0 : nat) (x1 : nat) := ((Nat.modulo x0 x1) = (Nat.modulo x0 x1)) -> False.
Definition term233 (x0 : nat) (x1 : nat) := ((Nat.div x0 x1) = (Nat.div x0 x1)) -> False.
Definition term21 := fun y0 : nat => forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0.
Definition term16 := fun y0 : nat => forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0.
Definition term23 := and (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0).
Definition term119 := fun y0 : nat => ((fun y1 : nat => exists y2 : nat, exists y3 : nat, (((Nat.div y2 y1) = (Nat.div y3 y1)) /\ ((Nat.modulo y2 y1) = (Nat.modulo y3 y1))) /\ (~ (y2 = y3))) y0) \/ ((fun y1 : nat => exists y2 : nat, exists y3 : nat, ((~ ((Nat.div y2 y1) = (Nat.div y3 y1))) \/ (~ ((Nat.modulo y2 y1) = (Nat.modulo y3 y1)))) /\ (y2 = y3)) y0).
Definition term97 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => exists y2 : nat, (((Nat.div y1 x0) = (Nat.div y2 x0)) /\ ((Nat.modulo y1 x0) = (Nat.modulo y2 x0))) /\ (~ (y1 = y2))) y0) \/ ((fun y1 : nat => exists y2 : nat, ((~ ((Nat.div y1 x0) = (Nat.div y2 x0))) \/ (~ ((Nat.modulo y1 x0) = (Nat.modulo y2 x0)))) /\ (y1 = y2)) y0).
Definition term58 (x0 : nat) := ~ ((fun y0 : nat => forall y1 : nat, forall y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) = (y1 = y2)) x0).
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (((Nat.div x1 x0) = (Nat.div x2 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo x2 x0)))) /\ (x1 = x2).
Definition term116 (x0 : nat) := or ((fun y0 : nat => exists y1 : nat, exists y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) /\ (~ (y1 = y2))) x0).
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) := (((Nat.div x1 x0) = (Nat.div x2 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo x2 x0))) /\ (~ (x1 = x2)).
Definition term197 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x1)) \/ (((Nat.add x0 x2) = (Nat.add x1 x3)) \/ (~ (x2 = x3))).
Definition term170 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x1)) \/ (((Nat.mul x0 x2) = (Nat.mul x1 x3)) \/ (~ (x2 = x3))).
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((((Nat.div x1 x0) = (Nat.div x2 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo x2 x0))) = (x1 = x2)).
Definition term19 (x0 : nat) := fun y0 : nat => (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0)) = x0.
Definition term145 (x0 : nat) (x1 : nat) := ~ ((Nat.div x0 x1) = (Nat.div x0 x1)).
Definition term217 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x1 = x0)) \/ (~ (x1 = x2))).
Definition term180 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term161 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = x2) -> (~ (x1 = x3)) \/ ((Nat.add x0 x1) = (Nat.add x2 x3)).
Definition term157 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = x2) -> (~ (x1 = x3)) \/ ((Nat.mul x0 x1) = (Nat.mul x2 x3)).
Definition term56 := exists y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, forall y3 : nat, (((Nat.div y2 y1) = (Nat.div y3 y1)) /\ ((Nat.modulo y2 y1) = (Nat.modulo y3 y1))) = (y2 = y3)) y0).
Definition term50 (x0 : nat) := exists y0 : nat, ~ ((fun y1 : nat => forall y2 : nat, (((Nat.div y1 x0) = (Nat.div y2 x0)) /\ ((Nat.modulo y1 x0) = (Nat.modulo y2 x0))) = (y1 = y2)) y0).
Definition term43 (x0 : nat) (x1 : nat) := exists y0 : nat, ~ ((fun y1 : nat => (((Nat.div x1 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo y1 x0))) = (x1 = y1)) y0).
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) := or ((fun y0 : nat => (((Nat.div x1 x0) = (Nat.div y0 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo y0 x0))) /\ (~ (x1 = y0))) x2).
Definition term130 := (exists y0 : nat, exists y1 : nat, exists y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) /\ (~ (y1 = y2))) \/ (exists y0 : nat, exists y1 : nat, exists y2 : nat, ((~ ((Nat.div y1 y0) = (Nat.div y2 y0))) \/ (~ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0)))) /\ (y1 = y2)).
Definition term108 (x0 : nat) := (exists y0 : nat, exists y1 : nat, (((Nat.div y0 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0))) /\ (~ (y0 = y1))) \/ (exists y0 : nat, exists y1 : nat, ((~ ((Nat.div y0 x0) = (Nat.div y1 x0))) \/ (~ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0)))) /\ (y0 = y1)).
Definition term155 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term193 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Nat.mul x2 (Nat.div x0 x2)) = (Nat.mul x2 (Nat.div x1 x2)))) -> (Nat.mul x2 (Nat.div x0 x2)) = (Nat.mul x2 (Nat.div x1 x2)).
Definition term177 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x1)) \/ (~ (x2 = x3)).
Definition term176 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((~ (x0 = x2)) \/ (~ (x1 = x3)))) -> (Nat.mul x0 x1) = (Nat.mul x2 x3).
Definition term109 := fun y0 : nat => (exists y1 : nat, exists y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) /\ (~ (y1 = y2))) \/ (exists y1 : nat, exists y2 : nat, ((~ ((Nat.div y1 y0) = (Nat.div y2 y0))) \/ (~ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0)))) /\ (y1 = y2)).
Definition term162 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((Nat.add x0 x1) = (Nat.add x2 x3))).
Definition term158 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ ((Nat.mul x0 x1) = (Nat.mul x2 x3))).
Definition term117 (x0 : nat) := (fun y0 : nat => exists y1 : nat, exists y2 : nat, ((~ ((Nat.div y1 y0) = (Nat.div y2 y0))) \/ (~ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0)))) /\ (y1 = y2)) x0.
Definition term115 (x0 : nat) := (fun y0 : nat => exists y1 : nat, exists y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) /\ (~ (y1 = y2))) x0.
Definition term8 := ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> False.
Definition term221 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((x1 = x0) /\ (x1 = x2)).
Definition term128 := exists y0 : nat, (fun y1 : nat => exists y2 : nat, exists y3 : nat, ((~ ((Nat.div y2 y1) = (Nat.div y3 y1))) \/ (~ ((Nat.modulo y2 y1) = (Nat.modulo y3 y1)))) /\ (y2 = y3)) y0.
Definition term123 := exists y0 : nat, (fun y1 : nat => exists y2 : nat, exists y3 : nat, (((Nat.div y2 y1) = (Nat.div y3 y1)) /\ ((Nat.modulo y2 y1) = (Nat.modulo y3 y1))) /\ (~ (y2 = y3))) y0.
Definition term106 (x0 : nat) := exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((~ ((Nat.div y1 x0) = (Nat.div y2 x0))) \/ (~ ((Nat.modulo y1 x0) = (Nat.modulo y2 x0)))) /\ (y1 = y2)) y0.
Definition term101 (x0 : nat) := exists y0 : nat, (fun y1 : nat => exists y2 : nat, (((Nat.div y1 x0) = (Nat.div y2 x0)) /\ ((Nat.modulo y1 x0) = (Nat.modulo y2 x0))) /\ (~ (y1 = y2))) y0.
Definition term129 := exists y0 : nat, exists y1 : nat, exists y2 : nat, ((~ ((Nat.div y1 y0) = (Nat.div y2 y0))) \/ (~ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0)))) /\ (y1 = y2).
Definition term124 := exists y0 : nat, exists y1 : nat, exists y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) /\ (~ (y1 = y2)).
Definition term107 (x0 : nat) := exists y0 : nat, exists y1 : nat, ((~ ((Nat.div y0 x0) = (Nat.div y1 x0))) \/ (~ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0)))) /\ (y0 = y1).
Definition term102 (x0 : nat) := exists y0 : nat, exists y1 : nat, (((Nat.div y0 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0))) /\ (~ (y0 = y1)).
Definition term61 := exists y0 : nat, exists y1 : nat, exists y2 : nat, ((((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) /\ (~ (y1 = y2))) \/ (((~ ((Nat.div y1 y0) = (Nat.div y2 y0))) \/ (~ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0)))) /\ (y1 = y2)).
Definition term55 (x0 : nat) := exists y0 : nat, exists y1 : nat, ((((Nat.div y0 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0))) /\ (~ (y0 = y1))) \/ (((~ ((Nat.div y0 x0) = (Nat.div y1 x0))) \/ (~ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0)))) /\ (y0 = y1)).
Definition term6 := (((~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) = (y1 = y2))) -> ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) = (y1 = y2))) -> ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) = (y1 = y2))) -> ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> False.
Definition term64 (x0 : nat -> Prop) (x1 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ (x1 y0).
Definition term46 (x0 : nat) (x1 : nat) := fun y0 : nat => ~ ((fun y1 : nat => (((Nat.div x1 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo y1 x0))) = (x1 = y1)) y0).
Definition term209 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = x2)) \/ (x1 = x2).
Definition term75 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (((Nat.div x1 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo y1 x0))) /\ (~ (x1 = y1))) y0) \/ ((fun y1 : nat => ((~ ((Nat.div x1 x0) = (Nat.div y1 x0))) \/ (~ ((Nat.modulo x1 x0) = (Nat.modulo y1 x0)))) /\ (x1 = y1)) y0).
Definition term125 := or (exists y0 : nat, (fun y1 : nat => exists y2 : nat, exists y3 : nat, (((Nat.div y2 y1) = (Nat.div y3 y1)) /\ ((Nat.modulo y2 y1) = (Nat.modulo y3 y1))) /\ (~ (y2 = y3))) y0).
Definition term103 (x0 : nat) := or (exists y0 : nat, (fun y1 : nat => exists y2 : nat, (((Nat.div y1 x0) = (Nat.div y2 x0)) /\ ((Nat.modulo y1 x0) = (Nat.modulo y2 x0))) /\ (~ (y1 = y2))) y0).
Definition term81 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (fun y1 : nat => (((Nat.div x1 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo y1 x0))) /\ (~ (x1 = y1))) y0).
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) := ((((Nat.div x1 x0) = (Nat.div x2 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo x2 x0))) /\ (~ (x1 = x2))) \/ (((~ ((Nat.div x1 x0) = (Nat.div x2 x0))) \/ (~ ((Nat.modulo x1 x0) = (Nat.modulo x2 x0)))) /\ (x1 = x2)).
Definition term183 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term7 := (((~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) = (y1 = y2))) -> ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) = (y1 = y2))) -> ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> False) -> ((~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) = (y1 = y2))) -> ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) = (y1 = y2))) -> ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> False.
Definition term149 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ~ ((Nat.modulo y0 x1) = (Nat.modulo x0 x1))) x2.
Definition term143 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ~ ((Nat.div y0 x1) = (Nat.div x0 x1))) x2.
Definition term169 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term140 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (Nat.mul y0 (Nat.div x0 y0)) (Nat.modulo x0 y0)) = x0) x1.
Definition term156 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x3)) \/ ((Nat.mul x0 x1) = (Nat.mul x2 x3)).
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat) := or ((((Nat.div x1 x0) = (Nat.div x2 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo x2 x0))) /\ (~ (x1 = x2))).
Definition term62 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term222 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = x1) /\ (x0 = x2)) -> x1 = x2.
Definition term41 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term223 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.add (Nat.mul x1 (Nat.div x2 x1)) (Nat.modulo x2 x1)) = (Nat.add (Nat.mul x1 (Nat.div x0 x1)) (Nat.modulo x0 x1))) /\ ((Nat.add (Nat.mul x1 (Nat.div x2 x1)) (Nat.modulo x2 x1)) = x2).
Definition term137 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Nat.div x0 x2) = (Nat.div x1 x2)).
Definition term65 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, x1 y0).
Definition term11 := imp (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) = (y1 = y2))).
Definition term29 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) = (y1 = y2).
Definition term208 (x0 : nat) (x1 : nat) := ~ ((Nat.add (Nat.mul x0 (Nat.div x1 x0)) (Nat.modulo x1 x0)) = x1).
Definition term5 := ((~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) = (y1 = y2))) -> ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> False) -> (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) = (y1 = y2))) -> ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)) -> False.
Definition term80 (x0 : nat) (x1 : nat) := exists y0 : nat, (((Nat.div x1 x0) = (Nat.div y0 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo y0 x0))) /\ (~ (x1 = y0)).
Definition term12 := (~ (forall y0 : nat, forall y1 : nat, forall y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) = (y1 = y2))) -> ~ ((forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1)) = y0) /\ (forall y0 : nat, forall y1 : nat, (Nat.add (Nat.mul y1 (Nat.div y0 y1)) (Nat.modulo y0 y1)) = y0)).
Definition term83 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => ((~ ((Nat.div x1 x0) = (Nat.div y1 x0))) \/ (~ ((Nat.modulo x1 x0) = (Nat.modulo y1 x0)))) /\ (x1 = y1)) y0.
Definition term136 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (((Nat.div x1 x0) = (Nat.div y0 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo y0 x0))) /\ (~ (x1 = y0))) \/ (exists y0 : nat, ((~ ((Nat.div x1 x0) = (Nat.div y0 x0))) \/ (~ ((Nat.modulo x1 x0) = (Nat.modulo y0 x0)))) /\ (x1 = y0))).
Definition term135 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (((Nat.div x1 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo x1 x0) = (Nat.modulo y1 x0))) /\ (~ (x1 = y1))) y0) \/ (exists y0 : nat, (fun y1 : nat => ((~ ((Nat.div x1 x0) = (Nat.div y1 x0))) \/ (~ ((Nat.modulo x1 x0) = (Nat.modulo y1 x0)))) /\ (x1 = y1)) y0)).
Definition term134 (x0 : nat) := @eq Prop ((exists y0 : nat, exists y1 : nat, (((Nat.div y0 x0) = (Nat.div y1 x0)) /\ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0))) /\ (~ (y0 = y1))) \/ (exists y0 : nat, exists y1 : nat, ((~ ((Nat.div y0 x0) = (Nat.div y1 x0))) \/ (~ ((Nat.modulo y0 x0) = (Nat.modulo y1 x0)))) /\ (y0 = y1))).
Definition term133 (x0 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => exists y2 : nat, (((Nat.div y1 x0) = (Nat.div y2 x0)) /\ ((Nat.modulo y1 x0) = (Nat.modulo y2 x0))) /\ (~ (y1 = y2))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, ((~ ((Nat.div y1 x0) = (Nat.div y2 x0))) \/ (~ ((Nat.modulo y1 x0) = (Nat.modulo y2 x0)))) /\ (y1 = y2)) y0)).
Definition term132 := @eq Prop ((exists y0 : nat, exists y1 : nat, exists y2 : nat, (((Nat.div y1 y0) = (Nat.div y2 y0)) /\ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0))) /\ (~ (y1 = y2))) \/ (exists y0 : nat, exists y1 : nat, exists y2 : nat, ((~ ((Nat.div y1 y0) = (Nat.div y2 y0))) \/ (~ ((Nat.modulo y1 y0) = (Nat.modulo y2 y0)))) /\ (y1 = y2))).
Definition term131 := @eq Prop ((exists y0 : nat, (fun y1 : nat => exists y2 : nat, exists y3 : nat, (((Nat.div y2 y1) = (Nat.div y3 y1)) /\ ((Nat.modulo y2 y1) = (Nat.modulo y3 y1))) /\ (~ (y2 = y3))) y0) \/ (exists y0 : nat, (fun y1 : nat => exists y2 : nat, exists y3 : nat, ((~ ((Nat.div y2 y1) = (Nat.div y3 y1))) \/ (~ ((Nat.modulo y2 y1) = (Nat.modulo y3 y1)))) /\ (y2 = y3)) y0)).
