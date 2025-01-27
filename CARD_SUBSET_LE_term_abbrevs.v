Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term135 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((~ (@FINITE a0 y0)) \/ ((~ (@SUBSET a0 x0 y0)) \/ (~ ((@CARD a0 x0) = (@CARD a0 y0))))) \/ (x0 = y0).
Definition term55 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0 -> Prop, ((@FINITE a0 y0) /\ ((@SUBSET a0 x0 y0) /\ (Peano.le (@CARD a0 y0) (@CARD a0 x0)))) /\ (~ (x0 = y0)).
Definition term237 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp (~ ((~ (@FINITE a0 x1)) \/ ((~ (@SUBSET a0 x0 x1)) \/ (~ ((@CARD a0 x0) = (@CARD a0 x1)))))).
Definition term168 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@SUBSET a0 x0 x1)) -> @SUBSET a0 x0 x1.
Definition term110 := fun y0 : nat => ((fun y1 : nat => forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, ((~ (Peano.le y1 y2)) \/ (~ (Peano.le y2 y1))) \/ (y1 = y2)) y0).
Definition term47 (a0 : Type') (x0 : type686 a0) := ~ (all x0).
Definition term241 := (~ False) -> False.
Definition term52 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ ((@SUBSET a0 x0 y0) /\ (Peano.le (@CARD a0 y0) (@CARD a0 x0)))) -> x0 = y0) x1).
Definition term217 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ ((@CARD a0 x0) = (@CARD a0 x1))) \/ ((x0 = x1) \/ (~ (@SUBSET a0 x0 x1))).
Definition term102 := forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, ((~ (Peano.le y1 y2)) \/ (~ (Peano.le y2 y1))) \/ (y1 = y2)) y0).
Definition term79 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => ((Peano.le x0 y1) /\ (Peano.le y1 x0)) \/ (~ (x0 = y1))) y0) /\ ((fun y1 : nat => ((~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 x0))) \/ (x0 = y1)) y0).
Definition term131 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ ((@FINITE a0 x1) /\ ((@SUBSET a0 x0 x1) /\ ((@CARD a0 x0) = (@CARD a0 x1))))) \/ (x0 = x1).
Definition term144 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((~ (@SUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1))) \/ (Peano.le (@CARD a0 x0) (@CARD a0 x1)).
Definition term188 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (@SUBSET a0 x0 x1).
Definition term138 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((@SUBSET a0 x0 x1) /\ (@FINITE a0 x1)).
Definition term185 (x0 : Prop) := ~ (~ x0).
Definition term66 (x0 : nat) (x1 : nat) := (~ ((Peano.le x0 x1) /\ (Peano.le x1 x0))) \/ (x0 = x1).
Definition term143 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ ((@SUBSET a0 x0 x1) /\ (@FINITE a0 x1))) \/ (Peano.le (@CARD a0 x0) (@CARD a0 x1)).
Definition term232 (a0 : Type') (x0 : a0 -> Prop) := and (~ (~ (@FINITE a0 x0))).
Definition term26 (a0 : Type') := (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ (Peano.le (@CARD a0 y1) (@CARD a0 y0)))) -> y0 = y1)) -> (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ ((@CARD a0 y0) = (@CARD a0 y1)))) -> y0 = y1) -> ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)).
Definition term222 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@FINITE a0 x1)) \/ ((~ ((@CARD a0 x0) = (@CARD a0 x1))) \/ (~ (@SUBSET a0 x0 x1))).
Definition term35 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) /\ (Peano.le x0 x1).
Definition term231 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (~ (@FINITE a0 x1))) /\ (~ ((~ (@SUBSET a0 x0 x1)) \/ (~ ((@CARD a0 x0) = (@CARD a0 x1))))).
Definition term88 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => ((Peano.le x0 y1) /\ (Peano.le y1 x0)) \/ (~ (x0 = y1))) y0) /\ ((fun y1 : nat => ((~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 x0))) \/ (x0 = y1)) y0).
Definition term163 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (x0 = x1).
Definition term171 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (Peano.le (@CARD a0 x0) (@CARD a0 x1)) \/ (~ (@SUBSET a0 x0 x1)).
Definition term155 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@FINITE a0 x1)) \/ (((~ (@SUBSET a0 x0 x1)) \/ (~ ((@CARD a0 x0) = (@CARD a0 x1)))) \/ (x0 = x1)).
Definition term24 (a0 : Type') := (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ ((@CARD a0 y0) = (@CARD a0 y1)))) -> y0 = y1) -> ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term83 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Peano.le x0 y0) /\ (Peano.le y0 x0)) \/ (~ (x0 = y0))) x1.
Definition term212 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ ((@CARD a0 x0) = (@CARD a0 x1))) -> (@CARD a0 x0) = (@CARD a0 x1).
Definition term146 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((~ (@SUBSET a0 x0 y0)) \/ (~ (@FINITE a0 y0))) \/ (Peano.le (@CARD a0 x0) (@CARD a0 y0)).
Definition term224 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (x0 = x1).
Definition term7 (x0 : Prop) := (~ x0) -> False.
Definition term103 := (forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) \/ (~ (y1 = y2))) y0) /\ (forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((~ (Peano.le y1 y2)) \/ (~ (Peano.le y2 y1))) \/ (y1 = y2)) y0).
Definition term80 (x0 : nat) := (forall y0 : nat, (fun y1 : nat => ((Peano.le x0 y1) /\ (Peano.le y1 x0)) \/ (~ (x0 = y1))) y0) /\ (forall y0 : nat, (fun y1 : nat => ((~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 x0))) \/ (x0 = y1)) y0).
Definition term121 := (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) \/ (~ (y0 = y1))) /\ (forall y0 : nat, forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y0))) \/ (y0 = y1)).
Definition term72 (x0 : nat) := forall y0 : nat, (((Peano.le x0 y0) /\ (Peano.le y0 x0)) \/ (~ (x0 = y0))) /\ (((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 x0))) \/ (x0 = y0)).
Definition term207 (x0 : nat) (x1 : nat) := imp (~ ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 x1)))).
Definition term98 (x0 : nat) := forall y0 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 x0))) \/ (x0 = y0).
Definition term82 (x0 : nat) := fun y0 : nat => ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 x0))) \/ (x0 = y0).
Definition term36 (x0 : nat) := fun y0 : nat => ((Peano.le x0 y0) /\ (Peano.le y0 x0)) = (x0 = y0).
Definition term240 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (x0 = x1) -> False.
Definition term37 (x0 : nat) := forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x0)) = (x0 = y0).
Definition term97 (x0 : nat) := forall y0 : nat, (fun y1 : nat => ((~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 x0))) \/ (x0 = y1)) y0.
Definition term92 (x0 : nat) := forall y0 : nat, (fun y1 : nat => ((Peano.le x0 y1) /\ (Peano.le y1 x0)) \/ (~ (x0 = y1))) y0.
Definition term128 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@SUBSET a0 x0 x1) /\ ((@CARD a0 x0) = (@CARD a0 x1)).
Definition term179 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term77 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term170 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@SUBSET a0 x0 x1)) \/ (Peano.le (@CARD a0 x0) (@CARD a0 x1)).
Definition term141 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (~ ((@SUBSET a0 x0 x1) /\ (@FINITE a0 x1))).
Definition term71 (x0 : nat) := fun y0 : nat => (((Peano.le x0 y0) /\ (Peano.le y0 x0)) \/ (~ (x0 = y0))) /\ (((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 x0))) \/ (x0 = y0)).
Definition term193 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (Peano.le (@CARD a0 x0) (@CARD a0 x1)).
Definition term160 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((@CARD a0 x0) = (@CARD a0 x1)).
Definition term100 := fun y0 : nat => (forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) \/ (~ (y0 = y1))) /\ (forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y0))) \/ (y0 = y1)).
Definition term19 (a0 : Type') := imp (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ ((@CARD a0 y0) = (@CARD a0 y1)))) -> y0 = y1).
Definition term157 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((~ (@SUBSET a0 x0 x1)) \/ (~ ((@CARD a0 x0) = (@CARD a0 x1)))) \/ (x0 = x1).
Definition term18 (a0 : Type') := ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)).
Definition term10 (a0 : Type') := ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ (Peano.le (@CARD a0 y1) (@CARD a0 y0)))) -> y0 = y1).
Definition term64 (x0 : nat) (x1 : nat) := or (~ ((Peano.le x1 x0) /\ (Peano.le x0 x1))).
Definition term167 (x0 : Prop) := (~ x0) -> x0.
Definition term59 (a0 : Type') := fun y0 : a0 -> Prop => ~ ((fun y1 : a0 -> Prop => forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ ((@SUBSET a0 y1 y2) /\ (Peano.le (@CARD a0 y2) (@CARD a0 y1)))) -> y1 = y2) y0).
Definition term158 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@SUBSET a0 x0 x1)) \/ ((~ ((@CARD a0 x0) = (@CARD a0 x1))) \/ (x0 = x1)).
Definition term130 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or ((~ (@FINITE a0 x1)) \/ ((~ (@SUBSET a0 x0 x1)) \/ (~ ((@CARD a0 x0) = (@CARD a0 x1))))).
Definition term54 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ ((@SUBSET a0 x0 y0) /\ (Peano.le (@CARD a0 y0) (@CARD a0 x0)))) /\ (~ (x0 = y0)).
Definition term182 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term236 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ ((@CARD a0 x0) = (@CARD a0 x1))).
Definition term145 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@SUBSET a0 x0 x1) /\ (@FINITE a0 x1).
Definition term69 (x0 : nat) (x1 : nat) := (((Peano.le x0 x1) /\ (Peano.le x1 x0)) \/ (~ (x0 = x1))) /\ ((~ ((Peano.le x0 x1) /\ (Peano.le x1 x0))) \/ (x0 = x1)).
Definition term148 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((~ (@SUBSET a0 y0 y1)) \/ (~ (@FINITE a0 y1))) \/ (Peano.le (@CARD a0 y0) (@CARD a0 y1)).
Definition term30 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1).
Definition term23 (a0 : Type') := (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ ((@CARD a0 y0) = (@CARD a0 y1)))) -> y0 = y1) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False.
Definition term112 := @eq Prop (forall y0 : nat, (forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) \/ (~ (y0 = y1))) /\ (forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y0))) \/ (y0 = y1))).
Definition term111 := @eq Prop (forall y0 : nat, ((fun y1 : nat => forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) \/ (~ (y1 = y2))) y0) /\ ((fun y1 : nat => forall y2 : nat, ((~ (Peano.le y1 y2)) \/ (~ (Peano.le y2 y1))) \/ (y1 = y2)) y0)).
Definition term90 (x0 : nat) := @eq Prop (forall y0 : nat, (((Peano.le x0 y0) /\ (Peano.le y0 x0)) \/ (~ (x0 = y0))) /\ (((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 x0))) \/ (x0 = y0))).
Definition term89 (x0 : nat) := @eq Prop (forall y0 : nat, ((fun y1 : nat => ((Peano.le x0 y1) /\ (Peano.le y1 x0)) \/ (~ (x0 = y1))) y0) /\ ((fun y1 : nat => ((~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 x0))) \/ (x0 = y1)) y0)).
Definition term239 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (x0 = x1)) -> x0 = x1.
Definition term76 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term20 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ ((@CARD a0 y0) = (@CARD a0 y1)))) -> y0 = y1) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False.
Definition term190 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp (~ ((~ (@SUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1)))).
Definition term229 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ ((~ (@FINITE a0 x1)) \/ ((~ (@SUBSET a0 x0 x1)) \/ (~ ((@CARD a0 x0) = (@CARD a0 x1)))))) -> x0 = x1.
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term127 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((@FINITE a0 x1) /\ ((@SUBSET a0 x0 x1) /\ ((@CARD a0 x0) = (@CARD a0 x1)))).
Definition term122 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((@SUBSET a0 x0 x1) /\ ((@CARD a0 x0) = (@CARD a0 x1))).
Definition term226 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((~ (@FINITE a0 x1)) \/ ((~ (@SUBSET a0 x0 x1)) \/ ((~ ((@CARD a0 x0) = (@CARD a0 x1))) \/ (x0 = x1)))).
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ ((@SUBSET a0 x0 y0) /\ (Peano.le (@CARD a0 y0) (@CARD a0 x0)))) -> x0 = y0) x1.
Definition term200 (x0 : nat) (x1 : nat) := @eq Prop ((x1 = x0) \/ ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 x1)))).
Definition term105 := fun y0 : nat => forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y0))) \/ (y0 = y1).
Definition term38 := fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1).
Definition term228 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (x0 = x1) \/ ((~ (@FINITE a0 x1)) \/ ((~ (@SUBSET a0 x0 x1)) \/ (~ ((@CARD a0 x0) = (@CARD a0 x1))))).
Definition term220 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (x0 = x1) \/ ((~ (@FINITE a0 x1)) \/ ((~ ((@CARD a0 x0) = (@CARD a0 x1))) \/ (~ (@SUBSET a0 x0 x1)))).
Definition term213 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ ((@CARD a0 x0) = (@CARD a0 x1))) \/ ((~ (@SUBSET a0 x0 x1)) \/ (x0 = x1)).
Definition term178 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (Peano.le (@CARD a0 x0) (@CARD a0 x1)) \/ ((~ (@SUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1))).
Definition term63 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 x1)).
Definition term41 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ ((@SUBSET a0 x0 y0) /\ (Peano.le (@CARD a0 y0) (@CARD a0 x0)))) -> x0 = y0.
Definition term32 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ ((@SUBSET a0 x0 y0) /\ ((@CARD a0 x0) = (@CARD a0 y0)))) -> x0 = y0.
Definition term162 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@SUBSET a0 x0 x1)) \/ ((~ (@FINITE a0 x1)) \/ (Peano.le (@CARD a0 x0) (@CARD a0 x1))).
Definition term195 (x0 : nat) (x1 : nat) := (x1 = x0) \/ (~ (Peano.le x0 x1)).
Definition term233 (a0 : Type') (x0 : a0 -> Prop) := and (@FINITE a0 x0).
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@SUBSET a0 x0 x1) /\ (@FINITE a0 x1)) -> Peano.le (@CARD a0 x0) (@CARD a0 x1).
Definition term29 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@SUBSET a0 x0 y0) /\ (@FINITE a0 y0)) -> Peano.le (@CARD a0 x0) (@CARD a0 y0).
Definition term165 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term91 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ((Peano.le x0 y1) /\ (Peano.le y1 x0)) \/ (~ (x0 = y1))) y0.
Definition term156 (a0 : Type') (x0 : a0 -> Prop) := ~ (@FINITE a0 x0).
Definition term198 (x0 : nat) (x1 : nat) := (x1 = x0) \/ ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 x1))).
Definition term58 (a0 : Type') (x0 : a0 -> Prop) := ~ ((fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ (Peano.le (@CARD a0 y1) (@CARD a0 y0)))) -> y0 = y1) x0).
Definition term17 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False.
Definition term134 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((~ (@FINITE a0 y0)) \/ ((~ (@SUBSET a0 x0 y0)) \/ (~ ((@CARD a0 x0) = (@CARD a0 y0))))) \/ (x0 = y0).
Definition term16 (a0 : Type') := (((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ (Peano.le (@CARD a0 y1) (@CARD a0 y0)))) -> y0 = y1)) -> (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ ((@CARD a0 y0) = (@CARD a0 y1)))) -> y0 = y1) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ (Peano.le (@CARD a0 y1) (@CARD a0 y0)))) -> y0 = y1)) -> (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ ((@CARD a0 y0) = (@CARD a0 y1)))) -> y0 = y1) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False) -> ((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ (Peano.le (@CARD a0 y1) (@CARD a0 y0)))) -> y0 = y1)) -> (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ ((@CARD a0 y0) = (@CARD a0 y1)))) -> y0 = y1) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ (Peano.le (@CARD a0 y1) (@CARD a0 y0)))) -> y0 = y1)) -> (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ ((@CARD a0 y0) = (@CARD a0 y1)))) -> y0 = y1) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False.
Definition term95 (x0 : nat) := and (forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x0)) \/ (~ (x0 = y0))).
Definition term14 (a0 : Type') := ((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ (Peano.le (@CARD a0 y1) (@CARD a0 y0)))) -> y0 = y1)) -> (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ ((@CARD a0 y0) = (@CARD a0 y1)))) -> y0 = y1) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ (Peano.le (@CARD a0 y1) (@CARD a0 y0)))) -> y0 = y1)) -> (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ ((@CARD a0 y0) = (@CARD a0 y1)))) -> y0 = y1) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False.
Definition term56 (a0 : Type') := exists y0 : a0 -> Prop, ~ ((fun y1 : a0 -> Prop => forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ ((@SUBSET a0 y1 y2) /\ (Peano.le (@CARD a0 y2) (@CARD a0 y1)))) -> y1 = y2) y0).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0 -> Prop, ~ ((fun y1 : a0 -> Prop => ((@FINITE a0 y1) /\ ((@SUBSET a0 x0 y1) /\ (Peano.le (@CARD a0 y1) (@CARD a0 x0)))) -> x0 = y1) y0).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term227 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((x0 = x1) \/ ((~ ((@CARD a0 x0) = (@CARD a0 x1))) \/ ((~ (@FINITE a0 x1)) \/ (~ (@SUBSET a0 x0 x1))))).
Definition term183 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((~ (@SUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1))).
Definition term181 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term126 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@FINITE a0 x1)) \/ ((~ (@SUBSET a0 x0 x1)) \/ (~ ((@CARD a0 x0) = (@CARD a0 x1)))).
Definition term123 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@SUBSET a0 x0 x1)) \/ (~ ((@CARD a0 x0) = (@CARD a0 x1))).
Definition term120 := forall y0 : nat, forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y0))) \/ (y0 = y1).
Definition term115 := forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) \/ (~ (y0 = y1)).
Definition term74 := forall y0 : nat, forall y1 : nat, (((Peano.le y0 y1) /\ (Peano.le y1 y0)) \/ (~ (y0 = y1))) /\ (((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y0))) \/ (y0 = y1)).
Definition term39 := forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1).
Definition term197 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) \/ ((x1 = x0) \/ (~ (Peano.le x0 x1))).
Definition term44 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (((@FINITE a0 x1) /\ ((@SUBSET a0 x0 x1) /\ (Peano.le (@CARD a0 x1) (@CARD a0 x0)))) -> x0 = x1).
Definition term53 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ~ ((fun y1 : a0 -> Prop => ((@FINITE a0 y1) /\ ((@SUBSET a0 x0 y1) /\ (Peano.le (@CARD a0 y1) (@CARD a0 x0)))) -> x0 = y1) y0).
Definition term109 (x0 : nat) := ((fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) \/ (~ (y0 = y1))) x0) /\ ((fun y0 : nat => forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y0))) \/ (y0 = y1)) x0).
Definition term124 (a0 : Type') (x0 : a0 -> Prop) := or (~ (@FINITE a0 x0)).
Definition term192 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (Peano.le (@CARD a0 x0) (@CARD a0 x1))) -> Peano.le (@CARD a0 x0) (@CARD a0 x1).
Definition term166 (a0 : Type') (x0 : a0 -> Prop) := (~ (@FINITE a0 x0)) -> @FINITE a0 x0.
Definition term70 (x0 : nat) (x1 : nat) := (((Peano.le x0 x1) /\ (Peano.le x1 x0)) \/ (~ (x0 = x1))) /\ (((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x0))) \/ (x0 = x1)).
Definition term15 (a0 : Type') := (((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ (Peano.le (@CARD a0 y1) (@CARD a0 y0)))) -> y0 = y1)) -> (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ ((@CARD a0 y0) = (@CARD a0 y1)))) -> y0 = y1) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ (Peano.le (@CARD a0 y1) (@CARD a0 y0)))) -> y0 = y1)) -> (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ ((@CARD a0 y0) = (@CARD a0 y1)))) -> y0 = y1) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ (Peano.le (@CARD a0 y1) (@CARD a0 y0)))) -> y0 = y1)) -> (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ ((@CARD a0 y0) = (@CARD a0 y1)))) -> y0 = y1) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False.
Definition term230 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((~ (@FINITE a0 x1)) \/ ((~ (@SUBSET a0 x0 x1)) \/ (~ ((@CARD a0 x0) = (@CARD a0 x1))))).
Definition term209 (x0 : nat) (x1 : nat) := ((Peano.le x0 x1) /\ (Peano.le x1 x0)) -> x0 = x1.
Definition term68 (x0 : nat) (x1 : nat) := and (((Peano.le x0 x1) /\ (Peano.le x1 x0)) \/ (~ (x0 = x1))).
Definition term93 (x0 : nat) := forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x0)) \/ (~ (x0 = y0)).
Definition term139 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@SUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1)).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term238 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp ((@FINITE a0 x1) /\ ((@SUBSET a0 x0 x1) /\ ((@CARD a0 x0) = (@CARD a0 x1)))).
Definition term62 (x0 : nat) (x1 : nat) := ~ ((Peano.le x1 x0) /\ (Peano.le x0 x1)).
Definition term153 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((~ (@SUBSET a0 y0 y1)) \/ (~ (@FINITE a0 y1))) \/ (Peano.le (@CARD a0 y0) (@CARD a0 y1))) x0.
Definition term151 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((~ (@FINITE a0 y1)) \/ ((~ (@SUBSET a0 y0 y1)) \/ (~ ((@CARD a0 y0) = (@CARD a0 y1))))) \/ (y0 = y1)) x0.
Definition term57 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ (Peano.le (@CARD a0 y1) (@CARD a0 y0)))) -> y0 = y1) x0.
Definition term133 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x1) /\ ((@SUBSET a0 x0 x1) /\ ((@CARD a0 x0) = (@CARD a0 x1))).
Definition term235 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (~ (@SUBSET a0 x0 x1))) /\ (~ (~ ((@CARD a0 x0) = (@CARD a0 x1)))).
Definition term65 (x0 : nat) (x1 : nat) := or ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 x1))).
Definition term9 (a0 : Type') := (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ (Peano.le (@CARD a0 y1) (@CARD a0 y0)))) -> y0 = y1)) -> False.
Definition term173 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (Peano.le (@CARD a0 x0) (@CARD a0 x1)) \/ ((~ (@FINITE a0 x1)) \/ (~ (@SUBSET a0 x0 x1))).
Definition term13 (a0 : Type') := (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ (Peano.le (@CARD a0 y1) (@CARD a0 y0)))) -> y0 = y1)) -> (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ ((@CARD a0 y0) = (@CARD a0 y1)))) -> y0 = y1) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False.
Definition term87 (x0 : nat) (x1 : nat) := ((fun y0 : nat => ((Peano.le x0 y0) /\ (Peano.le y0 x0)) \/ (~ (x0 = y0))) x1) /\ ((fun y0 : nat => ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 x0))) \/ (x0 = y0)) x1).
Definition term78 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term132 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((~ (@FINITE a0 x1)) \/ ((~ (@SUBSET a0 x0 x1)) \/ (~ ((@CARD a0 x0) = (@CARD a0 x1))))) \/ (x0 = x1).
Definition term221 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ ((@CARD a0 x0) = (@CARD a0 x1))) \/ (~ (@SUBSET a0 x0 x1)).
Definition term194 (x0 : nat) (x1 : nat) := (~ (Peano.le x1 x0)) \/ (x0 = x1).
Definition term125 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@FINITE a0 x1)) \/ (~ ((@SUBSET a0 x0 x1) /\ ((@CARD a0 x0) = (@CARD a0 x1)))).
Definition term164 (x0 : nat) (x1 : nat) := (~ (Peano.le x0 x1)) \/ ((~ (Peano.le x1 x0)) \/ (x0 = x1)).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term205 (x0 : nat) (x1 : nat) := and (~ (~ (Peano.le x0 x1))).
Definition term187 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (~ (~ (@SUBSET a0 x0 x1))).
Definition term196 (x0 : nat) (x1 : nat) := or (~ (Peano.le x0 x1)).
Definition term210 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (Peano.le (@CARD a0 x1) (@CARD a0 x0)) /\ (Peano.le (@CARD a0 x0) (@CARD a0 x1)).
Definition term149 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((~ (@SUBSET a0 y0 y1)) \/ (~ (@FINITE a0 y1))) \/ (Peano.le (@CARD a0 y0) (@CARD a0 y1)).
Definition term137 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((~ (@FINITE a0 y1)) \/ ((~ (@SUBSET a0 y0 y1)) \/ (~ ((@CARD a0 y0) = (@CARD a0 y1))))) \/ (y0 = y1).
Definition term12 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ ((@CARD a0 y0) = (@CARD a0 y1)))) -> y0 = y1.
Definition term11 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1).
Definition term8 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ (Peano.le (@CARD a0 y1) (@CARD a0 y0)))) -> y0 = y1.
Definition term219 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@FINITE a0 x1)) \/ ((x0 = x1) \/ ((~ ((@CARD a0 x0) = (@CARD a0 x1))) \/ (~ (@SUBSET a0 x0 x1)))).
Definition term48 (a0 : Type') (x0 : type686 a0) := exists y0 : a0 -> Prop, ~ (x0 y0).
Definition term184 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (~ (@SUBSET a0 x0 x1))) /\ (~ (~ (@FINITE a0 x1))).
Definition term176 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@FINITE a0 x1)) \/ (~ (@SUBSET a0 x0 x1)).
Definition term99 (x0 : nat) := (forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x0)) \/ (~ (x0 = y0))) /\ (forall y0 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 x0))) \/ (x0 = y0)).
Definition term46 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) /\ ((@SUBSET a0 x1 x0) /\ (Peano.le (@CARD a0 x0) (@CARD a0 x1))).
Definition term215 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (x0 = x1) \/ (~ (@SUBSET a0 x0 x1)).
Definition term117 := and (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) \/ (~ (y0 = y1))).
Definition term159 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (@SUBSET a0 x0 x1).
Definition term175 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((Peano.le (@CARD a0 x0) (@CARD a0 x1)) \/ ((~ (@FINITE a0 x1)) \/ (~ (@SUBSET a0 x0 x1)))).
Definition term177 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (Peano.le (@CARD a0 x0) (@CARD a0 x1)).
Definition term118 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, ((~ (Peano.le y1 y2)) \/ (~ (Peano.le y2 y1))) \/ (y1 = y2)) y0.
Definition term113 := fun y0 : nat => (fun y1 : nat => forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) \/ (~ (y1 = y2))) y0.
Definition term208 (x0 : nat) (x1 : nat) := imp ((Peano.le x1 x0) /\ (Peano.le x0 x1)).
Definition term108 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y0))) \/ (y0 = y1)) x0.
Definition term106 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) \/ (~ (y0 = y1))) x0.
Definition term172 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@FINITE a0 x1)) \/ ((Peano.le (@CARD a0 x0) (@CARD a0 x1)) \/ (~ (@SUBSET a0 x0 x1))).
Definition term60 (a0 : Type') := fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ (Peano.le (@CARD a0 y1) (@CARD a0 y0)))) /\ (~ (y0 = y1)).
Definition term152 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((~ (@FINITE a0 y0)) \/ ((~ (@SUBSET a0 x0 y0)) \/ (~ ((@CARD a0 x0) = (@CARD a0 y0))))) \/ (x0 = y0)) x1.
Definition term204 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term234 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((~ (@SUBSET a0 x0 x1)) \/ (~ ((@CARD a0 x0) = (@CARD a0 x1)))).
Definition term218 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (x0 = x1) \/ ((~ ((@CARD a0 x0) = (@CARD a0 x1))) \/ (~ (@SUBSET a0 x0 x1))).
Definition term174 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((~ (@SUBSET a0 x0 x1)) \/ ((~ (@FINITE a0 x1)) \/ (Peano.le (@CARD a0 x0) (@CARD a0 x1)))).
Definition term201 (x0 : nat) (x1 : nat) := (~ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x0)))) -> x0 = x1.
Definition term61 (a0 : Type') := exists y0 : a0 -> Prop, exists y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ (Peano.le (@CARD a0 y1) (@CARD a0 y0)))) /\ (~ (y0 = y1)).
Definition term202 (x0 : nat) (x1 : nat) := ~ ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 x1))).
Definition term84 (x0 : nat) (x1 : nat) := ((Peano.le x0 x1) /\ (Peano.le x1 x0)) \/ (~ (x0 = x1)).
Definition term191 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp ((@SUBSET a0 x0 x1) /\ (@FINITE a0 x1)).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) := ~ (forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ ((@SUBSET a0 x0 y0) /\ (Peano.le (@CARD a0 y0) (@CARD a0 x0)))) -> x0 = y0).
Definition term96 (x0 : nat) := fun y0 : nat => (fun y1 : nat => ((~ (Peano.le x0 y1)) \/ (~ (Peano.le y1 x0))) \/ (x0 = y1)) y0.
Definition term21 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ ((@CARD a0 y0) = (@CARD a0 y1)))) -> y0 = y1) -> ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)).
Definition term67 (x0 : nat) (x1 : nat) := ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x0))) \/ (x0 = x1).
Definition term116 := and (forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) \/ (~ (y1 = y2))) y0).
Definition term94 (x0 : nat) := and (forall y0 : nat, (fun y1 : nat => ((Peano.le x0 y1) /\ (Peano.le y1 x0)) \/ (~ (x0 = y1))) y0).
Definition term189 (a0 : Type') (x0 : a0 -> Prop) := ~ (~ (@FINITE a0 x0)).
Definition term107 (x0 : nat) := and ((fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) \/ (~ (y0 = y1))) x0).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term199 (x0 : nat) (x1 : nat) := @eq Prop ((~ (Peano.le x0 x1)) \/ ((~ (Peano.le x1 x0)) \/ (x0 = x1))).
Definition term104 := fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) \/ (~ (y0 = y1)).
Definition term129 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (~ ((@FINITE a0 x1) /\ ((@SUBSET a0 x0 x1) /\ ((@CARD a0 x0) = (@CARD a0 x1))))).
Definition term75 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term101 := forall y0 : nat, (forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) \/ (~ (y0 = y1))) /\ (forall y1 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y0))) \/ (y0 = y1)).
Definition term85 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => ((Peano.le x0 y0) /\ (Peano.le y0 x0)) \/ (~ (x0 = y0))) x1).
Definition term214 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@SUBSET a0 x0 x1)) \/ (x0 = x1).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term28 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((@SUBSET a0 x0 y0) /\ (@FINITE a0 y0)) -> Peano.le (@CARD a0 x0) (@CARD a0 y0).
Definition term147 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((~ (@SUBSET a0 x0 y0)) \/ (~ (@FINITE a0 y0))) \/ (Peano.le (@CARD a0 x0) (@CARD a0 y0)).
Definition term211 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((Peano.le (@CARD a0 x0) (@CARD a0 x1)) /\ (Peano.le (@CARD a0 x1) (@CARD a0 x0))) -> (@CARD a0 x0) = (@CARD a0 x1).
Definition term86 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 x0))) \/ (x0 = y0)) x1.
Definition term81 (x0 : nat) := fun y0 : nat => ((Peano.le x0 y0) /\ (Peano.le y0 x0)) \/ (~ (x0 = y0)).
Definition term119 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((~ (Peano.le y1 y2)) \/ (~ (Peano.le y2 y1))) \/ (y1 = y2)) y0.
Definition term114 := forall y0 : nat, (fun y1 : nat => forall y2 : nat, ((Peano.le y1 y2) /\ (Peano.le y2 y1)) \/ (~ (y1 = y2))) y0.
Definition term22 := imp (forall y0 : nat, forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)).
Definition term216 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (~ ((@CARD a0 x0) = (@CARD a0 x1))).
Definition term186 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ (@SUBSET a0 x0 x1)).
Definition term154 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((~ (@SUBSET a0 x0 y0)) \/ (~ (@FINITE a0 y0))) \/ (Peano.le (@CARD a0 x0) (@CARD a0 y0))) x1.
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x1) /\ ((@SUBSET a0 x0 x1) /\ (Peano.le (@CARD a0 x1) (@CARD a0 x0)))) -> x0 = x1.
Definition term31 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x1) /\ ((@SUBSET a0 x0 x1) /\ ((@CARD a0 x0) = (@CARD a0 x1)))) -> x0 = x1.
Definition term203 (x0 : nat) (x1 : nat) := (~ (~ (Peano.le x1 x0))) /\ (~ (~ (Peano.le x0 x1))).
Definition term42 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ ((@SUBSET a0 x0 y0) /\ (Peano.le (@CARD a0 y0) (@CARD a0 x0)))) -> x0 = y0.
Definition term33 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ ((@SUBSET a0 x0 y0) /\ ((@CARD a0 x0) = (@CARD a0 y0)))) -> x0 = y0.
Definition term140 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := Peano.le (@CARD a0 x0) (@CARD a0 x1).
Definition term169 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@FINITE a0 x1)) \/ ((~ (@SUBSET a0 x0 x1)) \/ (Peano.le (@CARD a0 x0) (@CARD a0 x1))).
Definition term73 := fun y0 : nat => forall y1 : nat, (((Peano.le y0 y1) /\ (Peano.le y1 y0)) \/ (~ (y0 = y1))) /\ (((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y0))) \/ (y0 = y1)).
Definition term206 (x0 : nat) (x1 : nat) := and (Peano.le x0 x1).
Definition term150 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@SUBSET a0 x1 x0) /\ (Peano.le (@CARD a0 x0) (@CARD a0 x1)).
Definition term25 (a0 : Type') := imp (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ (Peano.le (@CARD a0 y1) (@CARD a0 y0)))) -> y0 = y1)).
Definition term136 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((~ (@FINITE a0 y1)) \/ ((~ (@SUBSET a0 y0 y1)) \/ (~ ((@CARD a0 y0) = (@CARD a0 y1))))) \/ (y0 = y1).
Definition term43 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ (Peano.le (@CARD a0 y1) (@CARD a0 y0)))) -> y0 = y1.
Definition term34 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@SUBSET a0 y0 y1) /\ ((@CARD a0 y0) = (@CARD a0 y1)))) -> y0 = y1.
Definition term142 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or ((~ (@SUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1))).
Definition term180 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ ((~ (@SUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1)))) -> Peano.le (@CARD a0 x0) (@CARD a0 x1).
Definition term161 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@FINITE a0 x1)) \/ ((~ (@SUBSET a0 x0 x1)) \/ ((~ ((@CARD a0 x0) = (@CARD a0 x1))) \/ (x0 = x1))).
Definition term225 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (x0 = x1) \/ ((~ ((@CARD a0 x0) = (@CARD a0 x1))) \/ ((~ (@FINITE a0 x1)) \/ (~ (@SUBSET a0 x0 x1)))).
Definition term45 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x1) /\ ((@SUBSET a0 x0 x1) /\ (Peano.le (@CARD a0 x1) (@CARD a0 x0)))) /\ (~ (x0 = x1)).
Definition term223 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ ((@CARD a0 x0) = (@CARD a0 x1))) \/ ((~ (@FINITE a0 x1)) \/ (~ (@SUBSET a0 x0 x1))).
