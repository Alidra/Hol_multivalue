Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := ~ ((@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) x1)).
Definition term115 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((~ (@FINITE a0 y1)) \/ (~ (@SUBSET a0 y0 y1))) \/ (@FINITE a0 y0).
Definition term30 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0.
Definition term197 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (~ (Peano.le (@CARD a0 x0) x1)) -> Peano.le (@CARD a0 x0) x1.
Definition term156 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@SUBSET a0 x0 x1)) -> @SUBSET a0 x0 x1.
Definition term168 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((~ (@FINITE a0 x1)) \/ (~ (@SUBSET a0 x0 x1))).
Definition term66 (a0 : Type') (x0 : type686 a0) := ~ (all x0).
Definition term57 (x0 : nat -> Prop) := ~ (all x0).
Definition term178 := (~ False) -> False.
Definition term127 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((fun y1 : a0 -> Prop => (~ (@FINITE a0 y1)) \/ (~ (@SUBSET a0 x0 y1))) y0) \/ (@FINITE a0 x0).
Definition term109 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or ((~ (@FINITE a0 x1)) \/ (~ (@SUBSET a0 x0 x1))).
Definition term83 (x0 : nat) (x1 : nat) (x2 : nat) := or (~ ((Peano.le x0 x1) /\ (Peano.le x1 x2))).
Definition term110 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ ((@FINITE a0 x0) /\ (@SUBSET a0 x1 x0))) \/ (@FINITE a0 x1).
Definition term55 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := (@SUBSET a0 x0 x1) /\ ((@FINITE a0 x1) /\ (Peano.le (@CARD a0 x1) x2)).
Definition term100 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((~ (@SUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1))) \/ (Peano.le (@CARD a0 x0) (@CARD a0 x1)).
Definition term192 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (@SUBSET a0 x0 x1).
Definition term94 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((@SUBSET a0 x0 x1) /\ (@FINITE a0 x1)).
Definition term170 (x0 : Prop) := ~ (~ x0).
Definition term144 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y2))) \/ (Peano.le y0 y2)) x0.
Definition term99 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ ((@SUBSET a0 x0 x1) /\ (@FINITE a0 x1))) \/ (Peano.le (@CARD a0 x0) (@CARD a0 x1)).
Definition term172 (a0 : Type') (x0 : a0 -> Prop) := and (~ (~ (@FINITE a0 x0))).
Definition term108 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (~ ((@FINITE a0 x1) /\ (@SUBSET a0 x0 x1))).
Definition term26 (a0 : Type') := (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : nat, ((@SUBSET a0 y0 y1) /\ ((@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) y2))) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) y2))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0).
Definition term151 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x1 x0)) \/ ((~ (Peano.le x0 x2)) \/ (Peano.le x1 x2)).
Definition term181 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (Peano.le (@CARD a0 x0) (@CARD a0 x1)) \/ (~ (@SUBSET a0 x0 x1)).
Definition term207 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (Peano.le x0 x1))) /\ (~ (~ (Peano.le x1 x2))).
Definition term24 (a0 : Type') := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0).
Definition term158 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) \/ (~ (@SUBSET a0 x0 x1)).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term8 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : nat, ((@SUBSET a0 y0 y1) /\ ((@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) y2))) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) y2).
Definition term102 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((~ (@SUBSET a0 x0 y0)) \/ (~ (@FINITE a0 y0))) \/ (Peano.le (@CARD a0 x0) (@CARD a0 y0)).
Definition term7 (x0 : Prop) := (~ x0) -> False.
Definition term211 (x0 : nat) (x1 : nat) (x2 : nat) := imp (~ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2)))).
Definition term175 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp (~ ((~ (@FINITE a0 x1)) \/ (~ (@SUBSET a0 x0 x1)))).
Definition term89 (x0 : nat) (x1 : nat) := forall y0 : nat, ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 y0))) \/ (Peano.le x1 y0).
Definition term114 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((~ (@FINITE a0 y0)) \/ (~ (@SUBSET a0 x0 y0))) \/ (@FINITE a0 x0).
Definition term76 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : nat, ((@SUBSET a0 y0 y1) /\ ((@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) y2))) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) y2)) x0.
Definition term121 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((fun y1 : a0 -> Prop => (~ (@FINITE a0 y1)) \/ (~ (@SUBSET a0 x0 y1))) y0) \/ (@FINITE a0 x0).
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x0) /\ (@SUBSET a0 x1 x0)) -> @FINITE a0 x1.
Definition term164 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term180 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@SUBSET a0 x0 x1)) \/ (Peano.le (@CARD a0 x0) (@CARD a0 x1)).
Definition term97 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (~ ((@SUBSET a0 x0 x1) /\ (@FINITE a0 x1))).
Definition term113 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((~ (@FINITE a0 y0)) \/ (~ (@SUBSET a0 x0 y0))) \/ (@FINITE a0 x0).
Definition term59 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (forall y0 : nat, ((@SUBSET a0 x1 x0) /\ ((@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) y0))) -> (@FINITE a0 x1) /\ (Peano.le (@CARD a0 x1) y0)).
Definition term196 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (Peano.le (@CARD a0 x0) (@CARD a0 x1)).
Definition term19 (a0 : Type') := imp (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)).
Definition term119 (a0 : Type') (x0 : type686 a0) (x1 : Prop) := forall y0 : a0 -> Prop, (x0 y0) \/ x1.
Definition term68 (a0 : Type') (x0 : a0 -> Prop) := ~ (forall y0 : a0 -> Prop, forall y1 : nat, ((@SUBSET a0 x0 y0) /\ ((@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) y1))) -> (@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) y1)).
Definition term18 (a0 : Type') := ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0).
Definition term10 (a0 : Type') := ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : nat, ((@SUBSET a0 y0 y1) /\ ((@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) y2))) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) y2)).
Definition term155 (x0 : Prop) := (~ x0) -> x0.
Definition term78 (a0 : Type') := fun y0 : a0 -> Prop => ~ ((fun y1 : a0 -> Prop => forall y2 : a0 -> Prop, forall y3 : nat, ((@SUBSET a0 y1 y2) /\ ((@FINITE a0 y2) /\ (Peano.le (@CARD a0 y2) y3))) -> (@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) y3)) y0).
Definition term72 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ~ ((fun y1 : a0 -> Prop => forall y2 : nat, ((@SUBSET a0 x0 y1) /\ ((@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) y2))) -> (@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) y2)) y0).
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := (fun y0 : nat => ((@SUBSET a0 x1 x0) /\ ((@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) y0))) -> (@FINITE a0 x1) /\ (Peano.le (@CARD a0 x1) y0)) x2.
Definition term167 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term203 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((~ (Peano.le x1 x0)) \/ ((~ (Peano.le x0 x2)) \/ (Peano.le x1 x2))).
Definition term101 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@SUBSET a0 x0 x1) /\ (@FINITE a0 x1).
Definition term104 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((~ (@SUBSET a0 y0 y1)) \/ (~ (@FINITE a0 y1))) \/ (Peano.le (@CARD a0 y0) (@CARD a0 y1)).
Definition term34 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1).
Definition term52 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := ((@SUBSET a0 x1 x0) /\ ((@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) x2))) /\ (~ ((@FINITE a0 x1) /\ (Peano.le (@CARD a0 x1) x2))).
Definition term23 (a0 : Type') := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) -> False.
Definition term122 (a0 : Type') (x0 : a0 -> Prop) := (forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (~ (@FINITE a0 y1)) \/ (~ (@SUBSET a0 x0 y1))) y0) \/ (@FINITE a0 x0).
Definition term204 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Peano.le x0 x2) \/ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2)))).
Definition term169 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (~ (@FINITE a0 x1))) /\ (~ (~ (@SUBSET a0 x0 x1))).
Definition term198 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x2)) \/ (Peano.le x1 x2).
Definition term20 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) -> False.
Definition term118 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (forall y0 : a0, x0 y0) \/ x1.
Definition term193 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp (~ ((~ (@SUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1)))).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term136 (a0 : Type') := fun y0 : a0 -> Prop => (forall y1 : a0 -> Prop, (~ (@FINITE a0 y1)) \/ (~ (@SUBSET a0 y0 y1))) \/ (@FINITE a0 y0).
Definition term145 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 y1))) \/ (Peano.le x0 y1)) x1.
Definition term70 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : nat, ((@SUBSET a0 x0 y0) /\ ((@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) y1))) -> (@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) y1)) x1.
Definition term90 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 y1))) \/ (Peano.le x0 y1).
Definition term38 (x0 : nat) := fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term28 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> @FINITE a0 x0.
Definition term187 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (Peano.le (@CARD a0 x0) (@CARD a0 x1)) \/ ((~ (@SUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1))).
Definition term165 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ ((~ (@FINITE a0 x0)) \/ (~ (@SUBSET a0 x1 x0)))) -> @FINITE a0 x1.
Definition term153 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@SUBSET a0 x0 x1)) \/ ((~ (@FINITE a0 x1)) \/ (Peano.le (@CARD a0 x0) (@CARD a0 x1))).
Definition term173 (a0 : Type') (x0 : a0 -> Prop) := and (@FINITE a0 x0).
Definition term149 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@FINITE a0 x0)) \/ ((~ (@SUBSET a0 x1 x0)) \/ (@FINITE a0 x1)).
Definition term126 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((fun y0 : a0 -> Prop => (~ (@FINITE a0 y0)) \/ (~ (@SUBSET a0 x1 y0))) x0) \/ (@FINITE a0 x1).
Definition term31 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@SUBSET a0 x0 x1) /\ (@FINITE a0 x1)) -> Peano.le (@CARD a0 x0) (@CARD a0 x1).
Definition term130 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => (~ (@FINITE a0 y1)) \/ (~ (@SUBSET a0 x0 y1))) y0.
Definition term33 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@SUBSET a0 x0 y0) /\ (@FINITE a0 y0)) -> Peano.le (@CARD a0 x0) (@CARD a0 y0).
Definition term152 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term88 (x0 : nat) (x1 : nat) := fun y0 : nat => ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 y0))) \/ (Peano.le x1 y0).
Definition term213 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := (Peano.le (@CARD a0 x0) (@CARD a0 x1)) /\ (Peano.le (@CARD a0 x1) x2).
Definition term140 (a0 : Type') (x0 : a0 -> Prop) := ~ (@FINITE a0 x0).
Definition term77 (a0 : Type') (x0 : a0 -> Prop) := ~ ((fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : nat, ((@SUBSET a0 y0 y1) /\ ((@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) y2))) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) y2)) x0).
Definition term17 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) -> False.
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term16 (a0 : Type') := (((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : nat, ((@SUBSET a0 y0 y1) /\ ((@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) y2))) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) y2))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : nat, ((@SUBSET a0 y0 y1) /\ ((@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) y2))) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) y2))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) -> False) -> ((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : nat, ((@SUBSET a0 y0 y1) /\ ((@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) y2))) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) y2))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : nat, ((@SUBSET a0 y0 y1) /\ ((@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) y2))) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) y2))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) -> False.
Definition term29 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> @FINITE a0 x0.
Definition term14 (a0 : Type') := ((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : nat, ((@SUBSET a0 y0 y1) /\ ((@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) y2))) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) y2))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : nat, ((@SUBSET a0 y0 y1) /\ ((@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) y2))) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) y2))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) -> False.
Definition term75 (a0 : Type') := exists y0 : a0 -> Prop, ~ ((fun y1 : a0 -> Prop => forall y2 : a0 -> Prop, forall y3 : nat, ((@SUBSET a0 y1 y2) /\ ((@FINITE a0 y2) /\ (Peano.le (@CARD a0 y2) y3))) -> (@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) y3)) y0).
Definition term69 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0 -> Prop, ~ ((fun y1 : a0 -> Prop => forall y2 : nat, ((@SUBSET a0 x0 y1) /\ ((@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) y2))) -> (@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) y2)) y0).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term112 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x1) /\ (@SUBSET a0 x0 x1).
Definition term189 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((~ (@SUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1))).
Definition term85 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((Peano.le x1 x0) /\ (Peano.le x0 x2))) \/ (Peano.le x1 x2).
Definition term166 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term93 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y2))) \/ (Peano.le y0 y2).
Definition term91 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((~ (Peano.le x0 y0)) \/ (~ (Peano.le y0 y1))) \/ (Peano.le x0 y1).
Definition term41 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term39 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term131 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (~ (@FINITE a0 y1)) \/ (~ (@SUBSET a0 x0 y1))) y0.
Definition term160 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@FINITE a0 x1)) \/ ((@FINITE a0 x0) \/ (~ (@SUBSET a0 x0 x1))).
Definition term62 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := ~ ((fun y0 : nat => ((@SUBSET a0 x1 x0) /\ ((@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) y0))) -> (@FINITE a0 x1) /\ (Peano.le (@CARD a0 x1) y0)) x2).
Definition term120 (a0 : Type') (x0 : type686 a0) (x1 : Prop) := (forall y0 : a0 -> Prop, x0 y0) \/ x1.
Definition term159 (a0 : Type') (x0 : a0 -> Prop) := or (~ (@FINITE a0 x0)).
Definition term79 (a0 : Type') := fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, exists y2 : nat, ((@SUBSET a0 y0 y1) /\ ((@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) y2))) /\ ((~ (@FINITE a0 y0)) \/ (~ (Peano.le (@CARD a0 y0) y2))).
Definition term195 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (Peano.le (@CARD a0 x0) (@CARD a0 x1))) -> Peano.le (@CARD a0 x0) (@CARD a0 x1).
Definition term154 (a0 : Type') (x0 : a0 -> Prop) := (~ (@FINITE a0 x0)) -> @FINITE a0 x0.
Definition term139 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop ((forall y0 : a0 -> Prop, (~ (@FINITE a0 y0)) \/ (~ (@SUBSET a0 x0 y0))) \/ (@FINITE a0 x0)).
Definition term138 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop ((forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (~ (@FINITE a0 y1)) \/ (~ (@SUBSET a0 x0 y1))) y0) \/ (@FINITE a0 x0)).
Definition term15 (a0 : Type') := (((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : nat, ((@SUBSET a0 y0 y1) /\ ((@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) y2))) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) y2))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : nat, ((@SUBSET a0 y0 y1) /\ ((@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) y2))) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) y2))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : nat, ((@SUBSET a0 y0 y1) /\ ((@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) y2))) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) y2))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) -> False.
Definition term135 (a0 : Type') (x0 : a0 -> Prop) := (forall y0 : a0 -> Prop, (~ (@FINITE a0 y0)) \/ (~ (@SUBSET a0 x0 y0))) \/ (@FINITE a0 x0).
Definition term157 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@SUBSET a0 x1 x0)) \/ (@FINITE a0 x1).
Definition term106 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((@FINITE a0 x1) /\ (@SUBSET a0 x0 x1)).
Definition term95 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@SUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1)).
Definition term214 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := ((Peano.le (@CARD a0 x1) (@CARD a0 x0)) /\ (Peano.le (@CARD a0 x0) x2)) -> Peano.le (@CARD a0 x1) x2.
Definition term64 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : nat => ((@SUBSET a0 x1 x0) /\ ((@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) y0))) /\ ((~ (@FINITE a0 x1)) \/ (~ (Peano.le (@CARD a0 x1) y0))).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term147 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((~ (@SUBSET a0 y0 y1)) \/ (~ (@FINITE a0 y1))) \/ (Peano.le (@CARD a0 y0) (@CARD a0 y1))) x0.
Definition term142 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((~ (@FINITE a0 y1)) \/ (~ (@SUBSET a0 y0 y1))) \/ (@FINITE a0 y0)) x0.
Definition term84 (x0 : nat) (x1 : nat) (x2 : nat) := or ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2))).
Definition term134 (a0 : Type') (x0 : a0 -> Prop) := or (forall y0 : a0 -> Prop, (~ (@FINITE a0 y0)) \/ (~ (@SUBSET a0 x0 y0))).
Definition term9 (a0 : Type') := (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : nat, ((@SUBSET a0 y0 y1) /\ ((@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) y2))) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) y2))) -> False.
Definition term183 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (Peano.le (@CARD a0 x0) (@CARD a0 x1)) \/ ((~ (@FINITE a0 x1)) \/ (~ (@SUBSET a0 x0 x1))).
Definition term53 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := ((@SUBSET a0 x1 x0) /\ ((@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) x2))) /\ ((~ (@FINITE a0 x1)) \/ (~ (Peano.le (@CARD a0 x1) x2))).
Definition term13 (a0 : Type') := (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : nat, ((@SUBSET a0 y0 y1) /\ ((@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) y2))) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) y2))) -> (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) -> False.
Definition term117 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := forall y0 : a0, (x0 y0) \/ x1.
Definition term125 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or ((fun y0 : a0 -> Prop => (~ (@FINITE a0 y0)) \/ (~ (@SUBSET a0 x0 y0))) x1).
Definition term129 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (forall y0 : a0 -> Prop, ((~ (@FINITE a0 y0)) \/ (~ (@SUBSET a0 x0 y0))) \/ (@FINITE a0 x0)).
Definition term128 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (forall y0 : a0 -> Prop, ((fun y1 : a0 -> Prop => (~ (@FINITE a0 y1)) \/ (~ (@SUBSET a0 x0 y1))) y0) \/ (@FINITE a0 x0)).
Definition term177 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> False.
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (~ (@FINITE a0 x0)) \/ (~ (Peano.le (@CARD a0 x0) x1)).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term212 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Peano.le x0 x1) /\ (Peano.le x1 x2)).
Definition term209 (x0 : nat) (x1 : nat) := and (~ (~ (Peano.le x0 x1))).
Definition term191 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (~ (~ (@SUBSET a0 x0 x1))).
Definition term37 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term200 (x0 : nat) (x1 : nat) := or (~ (Peano.le x0 x1)).
Definition term116 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((~ (@FINITE a0 y1)) \/ (~ (@SUBSET a0 y0 y1))) \/ (@FINITE a0 y0).
Definition term105 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((~ (@SUBSET a0 y0 y1)) \/ (~ (@FINITE a0 y1))) \/ (Peano.le (@CARD a0 y0) (@CARD a0 y1)).
Definition term46 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : nat, ((@SUBSET a0 x0 y0) /\ ((@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) y1))) -> (@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) y1).
Definition term12 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1).
Definition term11 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0.
Definition term143 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((~ (@FINITE a0 y0)) \/ (~ (@SUBSET a0 x0 y0))) \/ (@FINITE a0 x0)) x1.
Definition term67 (a0 : Type') (x0 : type686 a0) := exists y0 : a0 -> Prop, ~ (x0 y0).
Definition term190 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (~ (@SUBSET a0 x0 x1))) /\ (~ (~ (@FINITE a0 x1))).
Definition term107 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@FINITE a0 x1)) \/ (~ (@SUBSET a0 x0 x1)).
Definition term141 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := ~ (Peano.le (@CARD a0 x0) x1).
Definition term71 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((fun y0 : a0 -> Prop => forall y1 : nat, ((@SUBSET a0 x0 y0) /\ ((@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) y1))) -> (@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) y1)) x1).
Definition term150 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (@SUBSET a0 x0 x1).
Definition term185 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((Peano.le (@CARD a0 x0) (@CARD a0 x1)) \/ ((~ (@FINITE a0 x1)) \/ (~ (@SUBSET a0 x0 x1)))).
Definition term65 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : nat, ((@SUBSET a0 x1 x0) /\ ((@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) y0))) /\ ((~ (@FINITE a0 x1)) \/ (~ (Peano.le (@CARD a0 x1) y0))).
Definition term123 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (~ (@FINITE a0 y0)) \/ (~ (@SUBSET a0 x0 y0)).
Definition term186 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (Peano.le (@CARD a0 x0) (@CARD a0 x1)).
Definition term182 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@FINITE a0 x1)) \/ ((Peano.le (@CARD a0 x0) (@CARD a0 x1)) \/ (~ (@SUBSET a0 x0 x1))).
Definition term205 (x0 : nat) (x1 : nat) (x2 : nat) := (~ ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 x2)))) -> Peano.le x1 x2.
Definition term202 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x2) \/ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2))).
Definition term208 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term87 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term44 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : nat, ((@SUBSET a0 x1 x0) /\ ((@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) y0))) -> (@FINITE a0 x1) /\ (Peano.le (@CARD a0 x1) y0).
Definition term184 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((~ (@SUBSET a0 x0 x1)) \/ ((~ (@FINITE a0 x1)) \/ (Peano.le (@CARD a0 x0) (@CARD a0 x1)))).
Definition term133 (a0 : Type') (x0 : a0 -> Prop) := or (forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => (~ (@FINITE a0 y1)) \/ (~ (@SUBSET a0 x0 y1))) y0).
Definition term86 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 x2))) \/ (Peano.le x1 x2).
Definition term43 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : nat => ((@SUBSET a0 x1 x0) /\ ((@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) y0))) -> (@FINITE a0 x1) /\ (Peano.le (@CARD a0 x1) y0).
Definition term81 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Peano.le x0 x1) /\ (Peano.le x1 x2)).
Definition term74 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0 -> Prop, exists y1 : nat, ((@SUBSET a0 x0 y0) /\ ((@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) y1))) /\ ((~ (@FINITE a0 x0)) \/ (~ (Peano.le (@CARD a0 x0) y1))).
Definition term206 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2))).
Definition term60 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : nat, ~ ((fun y1 : nat => ((@SUBSET a0 x1 x0) /\ ((@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) y1))) -> (@FINITE a0 x1) /\ (Peano.le (@CARD a0 x1) y1)) y0).
Definition term163 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((@FINITE a0 x0) \/ ((~ (@FINITE a0 x1)) \/ (~ (@SUBSET a0 x0 x1)))).
Definition term215 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (Peano.le (@CARD a0 x0) x1) -> False.
Definition term54 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := ~ (((@SUBSET a0 x1 x0) /\ ((@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) x2))) -> (@FINITE a0 x1) /\ (Peano.le (@CARD a0 x1) x2)).
Definition term194 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp ((@SUBSET a0 x0 x1) /\ (@FINITE a0 x1)).
Definition term21 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0).
Definition term36 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term171 (a0 : Type') (x0 : a0 -> Prop) := ~ (~ (@FINITE a0 x0)).
Definition term82 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x1)) \/ (~ (Peano.le x1 x2)).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term161 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) \/ ((~ (@FINITE a0 x1)) \/ (~ (@SUBSET a0 x0 x1))).
Definition term132 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (~ (@FINITE a0 y0)) \/ (~ (@SUBSET a0 x0 y0)).
Definition term47 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : nat, ((@SUBSET a0 y0 y1) /\ ((@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) y2))) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) y2).
Definition term73 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => exists y1 : nat, ((@SUBSET a0 x0 y0) /\ ((@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) y1))) /\ ((~ (@FINITE a0 x0)) \/ (~ (Peano.le (@CARD a0 x0) y1))).
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => ((@SUBSET a0 x1 x0) /\ ((@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) y1))) -> (@FINITE a0 x1) /\ (Peano.le (@CARD a0 x1) y1)) y0).
Definition term45 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : nat, ((@SUBSET a0 x0 y0) /\ ((@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) y1))) -> (@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) y1).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term56 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) x1).
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := and ((@SUBSET a0 x0 x1) /\ ((@FINITE a0 x1) /\ (Peano.le (@CARD a0 x1) x2))).
Definition term32 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((@SUBSET a0 x0 y0) /\ (@FINITE a0 y0)) -> Peano.le (@CARD a0 x0) (@CARD a0 y0).
Definition term201 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x1)) \/ ((Peano.le x0 x2) \/ (~ (Peano.le x1 x2))).
Definition term103 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((~ (@SUBSET a0 x0 y0)) \/ (~ (@FINITE a0 y0))) \/ (Peano.le (@CARD a0 x0) (@CARD a0 y0)).
Definition term176 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp ((@FINITE a0 x1) /\ (@SUBSET a0 x0 x1)).
Definition term137 (a0 : Type') := forall y0 : a0 -> Prop, (forall y1 : a0 -> Prop, (~ (@FINITE a0 y1)) \/ (~ (@SUBSET a0 y0 y1))) \/ (@FINITE a0 y0).
Definition term42 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := ((@SUBSET a0 x1 x0) /\ ((@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) x2))) -> (@FINITE a0 x1) /\ (Peano.le (@CARD a0 x1) x2).
Definition term80 (a0 : Type') := exists y0 : a0 -> Prop, exists y1 : a0 -> Prop, exists y2 : nat, ((@SUBSET a0 y0 y1) /\ ((@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) y2))) /\ ((~ (@FINITE a0 y0)) \/ (~ (Peano.le (@CARD a0 y0) y2))).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := Peano.le (@CARD a0 x0) x1.
Definition term22 := imp (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2).
Definition term174 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ (@SUBSET a0 x0 x1)).
Definition term162 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((~ (@FINITE a0 x0)) \/ ((~ (@SUBSET a0 x1 x0)) \/ (@FINITE a0 x1))).
Definition term124 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (@FINITE a0 y0)) \/ (~ (@SUBSET a0 x0 y0))) x1.
Definition term148 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((~ (@SUBSET a0 x0 y0)) \/ (~ (@FINITE a0 y0))) \/ (Peano.le (@CARD a0 x0) (@CARD a0 y0))) x1.
Definition term58 (x0 : nat -> Prop) := exists y0 : nat, ~ (x0 y0).
Definition term199 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x2) \/ (~ (Peano.le x1 x2)).
Definition term146 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((~ (Peano.le x1 x0)) \/ (~ (Peano.le x0 y0))) \/ (Peano.le x1 y0)) x2.
Definition term96 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := Peano.le (@CARD a0 x0) (@CARD a0 x1).
Definition term179 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@FINITE a0 x1)) \/ ((~ (@SUBSET a0 x0 x1)) \/ (Peano.le (@CARD a0 x0) (@CARD a0 x1))).
Definition term111 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((~ (@FINITE a0 x0)) \/ (~ (@SUBSET a0 x1 x0))) \/ (@FINITE a0 x1).
Definition term210 (x0 : nat) (x1 : nat) := and (Peano.le x0 x1).
Definition term25 (a0 : Type') := imp (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : nat, ((@SUBSET a0 y0 y1) /\ ((@FINITE a0 y1) /\ (Peano.le (@CARD a0 y1) y2))) -> (@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) y2))).
Definition term92 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((~ (Peano.le y0 y1)) \/ (~ (Peano.le y1 y2))) \/ (Peano.le y0 y2).
Definition term40 := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term98 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or ((~ (@SUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1))).
Definition term188 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ ((~ (@SUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1)))) -> Peano.le (@CARD a0 x0) (@CARD a0 x1).
