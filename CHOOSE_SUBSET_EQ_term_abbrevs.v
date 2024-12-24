Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term85 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := ~ ((@FINITE a0 x0) /\ ((@CARD a0 x0) = x1)).
Definition term202 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term22 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term231 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp (~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3))))).
Definition term7 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0 -> Prop, ((@FINITE a0 y1) -> Peano.le y0 (@CARD a0 y1)) -> exists y2 : a0 -> Prop, (@SUBSET a0 y2 y1) /\ (@HAS_SIZE a0 y2 y0)) x0.
Definition term240 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@SUBSET a0 x0 x1)) -> @SUBSET a0 x0 x1.
Definition term201 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) \/ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3))).
Definition term239 := (~ False) -> False.
Definition term39 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (((@SUBSET a0 x1 x2) -> (@HAS_SIZE a0 x1 x0) -> (@FINITE a0 x2) -> (~ ((Peano.le x0 (@CARD a0 x1)) /\ (Peano.le (@CARD a0 x1) (@CARD a0 x2)))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False) -> (@SUBSET a0 x1 x2) -> (@HAS_SIZE a0 x1 x0) -> (@FINITE a0 x2) -> (~ ((Peano.le x0 (@CARD a0 x1)) /\ (Peano.le (@CARD a0 x1) (@CARD a0 x2)))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False) -> (@SUBSET a0 x1 x2) -> (@HAS_SIZE a0 x1 x0) -> (@FINITE a0 x2) -> (~ ((Peano.le x0 (@CARD a0 x1)) /\ (Peano.le (@CARD a0 x1) (@CARD a0 x2)))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False.
Definition term103 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : nat, ((fun y1 : nat => (@HAS_SIZE a0 x0 y1) \/ ((~ (@FINITE a0 x0)) \/ (~ ((@CARD a0 x0) = y1)))) y0) /\ ((fun y1 : nat => (~ (@HAS_SIZE a0 x0 y1)) \/ ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y1))) y0).
Definition term52 (a0 : Type') (x0 : a0 -> Prop) := imp (@FINITE a0 x0).
Definition term105 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : nat => (@HAS_SIZE a0 x0 y0) \/ ((~ (@FINITE a0 x0)) \/ (~ ((@CARD a0 x0) = y0))).
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : nat, (@SUBSET a0 x0 x1) -> (@HAS_SIZE a0 x0 y0) -> (@FINITE a0 x1) -> (~ ((Peano.le y0 (@CARD a0 x0)) /\ (Peano.le (@CARD a0 x0) (@CARD a0 x1)))) -> (forall y1 : nat, Peano.le y1 y1) -> (forall y1 : a0 -> Prop, forall y2 : nat, (@HAS_SIZE a0 y1 y2) = ((@FINITE a0 y1) /\ ((@CARD a0 y1) = y2))) -> ~ (forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, ((@SUBSET a0 y1 y2) /\ (@FINITE a0 y2)) -> Peano.le (@CARD a0 y1) (@CARD a0 y2)).
Definition term62 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : nat, (@SUBSET a0 x0 x1) -> (@HAS_SIZE a0 x0 y0) -> (@FINITE a0 x1) -> (~ ((Peano.le y0 (@CARD a0 x0)) /\ (Peano.le (@CARD a0 x0) (@CARD a0 x1)))) -> (forall y1 : nat, Peano.le y1 y1) -> (forall y1 : a0 -> Prop, forall y2 : nat, (@HAS_SIZE a0 y1 y2) = ((@FINITE a0 y1) /\ ((@CARD a0 y1) = y2))) -> (forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, ((@SUBSET a0 y1 y2) /\ (@FINITE a0 y2)) -> Peano.le (@CARD a0 y1) (@CARD a0 y2)) -> False.
Definition term152 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((~ (@SUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1))) \/ (Peano.le (@CARD a0 x0) (@CARD a0 x1)).
Definition term258 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (@SUBSET a0 x0 x1).
Definition term49 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := imp (~ ((Peano.le x0 (@CARD a0 x1)) /\ (Peano.le (@CARD a0 x1) (@CARD a0 x2)))).
Definition term147 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((@SUBSET a0 x0 x1) /\ (@FINITE a0 x1)).
Definition term190 (x0 : Prop) := ~ (~ x0).
Definition term14 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) x0.
Definition term273 (a0 : Type') (x0 : nat) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) -> Peano.le x0 (@CARD a0 y0)) = (exists y1 : a0 -> Prop, (@SUBSET a0 y1 y0) /\ (@HAS_SIZE a0 y1 x0)).
Definition term151 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ ((@SUBSET a0 x0 x1) /\ (@FINITE a0 x1))) \/ (Peano.le (@CARD a0 x0) (@CARD a0 x1)).
Definition term199 (a0 : Type') (x0 : a0 -> Prop) := (~ (Peano.le (@CARD a0 x0) (@CARD a0 x0))) -> Peano.le (@CARD a0 x0) (@CARD a0 x0).
Definition term111 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : nat => ((fun y1 : nat => (@HAS_SIZE a0 x0 y1) \/ ((~ (@FINITE a0 x0)) \/ (~ ((@CARD a0 x0) = y1)))) y0) /\ ((fun y1 : nat => (~ (@HAS_SIZE a0 x0 y1)) \/ ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y1))) y0).
Definition term10 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := ((@FINITE a0 x0) -> Peano.le x1 (@CARD a0 x0)) -> exists y0 : a0 -> Prop, (@SUBSET a0 y0 x0) /\ (@HAS_SIZE a0 y0 x1).
Definition term268 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 (@CARD a0 x1)).
Definition term244 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (Peano.le (@CARD a0 x0) (@CARD a0 x1)) \/ (~ (@SUBSET a0 x0 x1)).
Definition term227 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (~ (x2 = x0))) /\ (~ (~ (Peano.le x1 x2))).
Definition term27 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term116 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : nat, (@HAS_SIZE a0 x0 y0) \/ ((~ (@FINITE a0 x0)) \/ (~ ((@CARD a0 x0) = y0))).
Definition term57 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@HAS_SIZE a0 x1 x0) -> (@FINITE a0 x2) -> (~ ((Peano.le x0 (@CARD a0 x1)) /\ (Peano.le (@CARD a0 x1) (@CARD a0 x2)))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)).
Definition term56 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@HAS_SIZE a0 x1 x0) -> (@FINITE a0 x2) -> (~ ((Peano.le x0 (@CARD a0 x1)) /\ (Peano.le (@CARD a0 x1) (@CARD a0 x2)))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False.
Definition term200 (a0 : Type') (x0 : a0 -> Prop) := ~ (Peano.le (@CARD a0 x0) (@CARD a0 x0)).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term71 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : nat, (@SUBSET a0 y1 y0) -> (@HAS_SIZE a0 y1 y2) -> (@FINITE a0 y0) -> (~ ((Peano.le y2 (@CARD a0 y1)) /\ (Peano.le (@CARD a0 y1) (@CARD a0 y0)))) -> (forall y3 : nat, Peano.le y3 y3) -> (forall y3 : a0 -> Prop, forall y4 : nat, (@HAS_SIZE a0 y3 y4) = ((@FINITE a0 y3) /\ ((@CARD a0 y3) = y4))) -> ~ (forall y3 : a0 -> Prop, forall y4 : a0 -> Prop, ((@SUBSET a0 y3 y4) /\ (@FINITE a0 y4)) -> Peano.le (@CARD a0 y3) (@CARD a0 y4)).
Definition term70 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : nat, (@SUBSET a0 y1 y0) -> (@HAS_SIZE a0 y1 y2) -> (@FINITE a0 y0) -> (~ ((Peano.le y2 (@CARD a0 y1)) /\ (Peano.le (@CARD a0 y1) (@CARD a0 y0)))) -> (forall y3 : nat, Peano.le y3 y3) -> (forall y3 : a0 -> Prop, forall y4 : nat, (@HAS_SIZE a0 y3 y4) = ((@FINITE a0 y3) /\ ((@CARD a0 y3) = y4))) -> (forall y3 : a0 -> Prop, forall y4 : a0 -> Prop, ((@SUBSET a0 y3 y4) /\ (@FINITE a0 y4)) -> Peano.le (@CARD a0 y3) (@CARD a0 y4)) -> False.
Definition term154 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((~ (@SUBSET a0 x0 y0)) \/ (~ (@FINITE a0 y0))) \/ (Peano.le (@CARD a0 x0) (@CARD a0 y0)).
Definition term124 (a0 : Type') := forall y0 : a0 -> Prop, (forall y1 : nat, (@HAS_SIZE a0 y0 y1) \/ ((~ (@FINITE a0 y0)) \/ (~ ((@CARD a0 y0) = y1)))) /\ (forall y1 : nat, (~ (@HAS_SIZE a0 y0 y1)) \/ ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))).
Definition term31 (x0 : Prop) := (~ x0) -> False.
Definition term104 (a0 : Type') (x0 : a0 -> Prop) := (forall y0 : nat, (fun y1 : nat => (@HAS_SIZE a0 x0 y1) \/ ((~ (@FINITE a0 x0)) \/ (~ ((@CARD a0 x0) = y1)))) y0) /\ (forall y0 : nat, (fun y1 : nat => (~ (@HAS_SIZE a0 x0 y1)) \/ ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y1))) y0).
Definition term161 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : nat, ((~ (@HAS_SIZE a0 x0 y0)) \/ (@FINITE a0 x0)) /\ ((~ (@HAS_SIZE a0 x0 y0)) \/ ((@CARD a0 x0) = y0)).
Definition term159 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := ~ (@HAS_SIZE a0 x0 x1).
Definition term198 (a0 : Type') (x0 : a0 -> Prop) := Peano.le (@CARD a0 x0) (@CARD a0 x0).
Definition term8 (a0 : Type') (x0 : nat) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) -> Peano.le x0 (@CARD a0 y0)) -> exists y1 : a0 -> Prop, (@SUBSET a0 y1 y0) /\ (@HAS_SIZE a0 y1 x0).
Definition term210 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x3) \/ ((~ (x1 = x0)) \/ ((~ (Peano.le x1 x2)) \/ (~ (x2 = x3)))).
Definition term80 := fun y0 : nat => Peano.le y0 y0.
Definition term33 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (~ ((Peano.le x0 (@CARD a0 x1)) /\ (Peano.le (@CARD a0 x1) (@CARD a0 x2)))) -> False.
Definition term205 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (Peano.le x0 x1)) \/ (~ (x1 = x2)).
Definition term207 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x3) \/ ((~ (Peano.le x1 x2)) \/ (~ (x2 = x3))).
Definition term59 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@SUBSET a0 x1 x2) -> (@HAS_SIZE a0 x1 x0) -> (@FINITE a0 x2) -> (~ ((Peano.le x0 (@CARD a0 x1)) /\ (Peano.le (@CARD a0 x1) (@CARD a0 x2)))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)).
Definition term37 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@SUBSET a0 x1 x2) -> (@HAS_SIZE a0 x1 x0) -> (@FINITE a0 x2) -> (~ ((Peano.le x0 (@CARD a0 x1)) /\ (Peano.le (@CARD a0 x1) (@CARD a0 x2)))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False.
Definition term94 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := ((@HAS_SIZE a0 x0 x1) \/ ((~ (@FINITE a0 x0)) \/ (~ ((@CARD a0 x0) = x1)))) /\ ((~ (@HAS_SIZE a0 x0 x1)) \/ ((@FINITE a0 x0) /\ ((@CARD a0 x0) = x1))).
Definition term143 (a0 : Type') := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => forall y2 : nat, (~ (@HAS_SIZE a0 y1 y2)) \/ ((@FINITE a0 y1) /\ ((@CARD a0 y1) = y2))) y0.
Definition term138 (a0 : Type') := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => forall y2 : nat, (@HAS_SIZE a0 y1 y2) \/ ((~ (@FINITE a0 y1)) \/ (~ ((@CARD a0 y1) = y2)))) y0.
Definition term264 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : nat, (@SUBSET a0 y1 y0) -> (@HAS_SIZE a0 y1 y2) -> (@FINITE a0 y0) -> (~ ((Peano.le y2 (@CARD a0 y1)) /\ (Peano.le (@CARD a0 y1) (@CARD a0 y0)))) -> (forall y3 : nat, Peano.le y3 y3) -> (forall y3 : a0 -> Prop, forall y4 : nat, (@HAS_SIZE a0 y3 y4) = ((@FINITE a0 y3) /\ ((@CARD a0 y3) = y4))) -> (forall y3 : a0 -> Prop, forall y4 : a0 -> Prop, ((@SUBSET a0 y3 y4) /\ (@FINITE a0 y4)) -> Peano.le (@CARD a0 y3) (@CARD a0 y4)) -> False) x0.
Definition term120 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : nat, (fun y1 : nat => (~ (@HAS_SIZE a0 x0 y1)) \/ ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y1))) y0.
Definition term115 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : nat, (fun y1 : nat => (@HAS_SIZE a0 x0 y1) \/ ((~ (@FINITE a0 x0)) \/ (~ ((@CARD a0 x0) = y1)))) y0.
Definition term194 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (~ ((@CARD a0 x0) = x1)) -> (@CARD a0 x0) = x1.
Definition term209 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x0)) \/ ((Peano.le x0 x3) \/ ((~ (Peano.le x1 x2)) \/ (~ (x2 = x3)))).
Definition term21 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> Peano.le x0 x1.
Definition term270 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := fun y0 : a0 -> Prop => (@SUBSET a0 y0 x0) /\ (@HAS_SIZE a0 y0 x1).
Definition term188 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term189 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (~ (~ (@HAS_SIZE a0 x0 x1))) -> (@CARD a0 x0) = x1.
Definition term101 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (x0 y0) /\ (x1 y0).
Definition term225 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term95 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : nat => ((@HAS_SIZE a0 x0 y0) \/ ((~ (@FINITE a0 x0)) \/ (~ ((@CARD a0 x0) = y0)))) /\ ((~ (@HAS_SIZE a0 x0 y0)) \/ ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0))).
Definition term243 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@SUBSET a0 x0 x1)) \/ (Peano.le (@CARD a0 x0) (@CARD a0 x1)).
Definition term46 := imp (forall y0 : nat, Peano.le y0 y0).
Definition term149 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (~ ((@SUBSET a0 x0 x1) /\ (@FINITE a0 x1))).
Definition term25 (x0 : nat) := forall y0 : nat, (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0.
Definition term165 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (Peano.le (@CARD a0 x0) (@CARD a0 x1)).
Definition term43 (a0 : Type') := imp (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))).
Definition term218 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((~ (x0 = x2)) \/ ((~ (x1 = x3)) \/ (~ (Peano.le x0 x1))))) -> Peano.le x2 x3.
Definition term237 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := (~ (Peano.le x0 (@CARD a0 x1))) -> Peano.le x0 (@CARD a0 x1).
Definition term58 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp (@SUBSET a0 x0 x1).
Definition term42 (a0 : Type') := ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)).
Definition term184 (x0 : Prop) := (~ x0) -> x0.
Definition term83 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := Peano.le x0 (@CARD a0 x1).
Definition term92 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := and ((@HAS_SIZE a0 x0 x1) \/ ((~ (@FINITE a0 x0)) \/ (~ ((@CARD a0 x0) = x1)))).
Definition term220 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : nat => (@SUBSET a0 x0 x1) -> (@HAS_SIZE a0 x0 y0) -> (@FINITE a0 x1) -> (~ ((Peano.le y0 (@CARD a0 x0)) /\ (Peano.le (@CARD a0 x0) (@CARD a0 x1)))) -> (forall y1 : nat, Peano.le y1 y1) -> (forall y1 : a0 -> Prop, forall y2 : nat, (@HAS_SIZE a0 y1 y2) = ((@FINITE a0 y1) /\ ((@CARD a0 y1) = y2))) -> ~ (forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, ((@SUBSET a0 y1 y2) /\ (@FINITE a0 y2)) -> Peano.le (@CARD a0 y1) (@CARD a0 y2)).
Definition term60 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : nat => (@SUBSET a0 x0 x1) -> (@HAS_SIZE a0 x0 y0) -> (@FINITE a0 x1) -> (~ ((Peano.le y0 (@CARD a0 x0)) /\ (Peano.le (@CARD a0 x0) (@CARD a0 x1)))) -> (forall y1 : nat, Peano.le y1 y1) -> (forall y1 : a0 -> Prop, forall y2 : nat, (@HAS_SIZE a0 y1 y2) = ((@FINITE a0 y1) /\ ((@CARD a0 y1) = y2))) -> (forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, ((@SUBSET a0 y1 y2) /\ (@FINITE a0 y2)) -> Peano.le (@CARD a0 y1) (@CARD a0 y2)) -> False.
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0) x2.
Definition term191 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := ~ (~ (@HAS_SIZE a0 x0 x1)).
Definition term153 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@SUBSET a0 x0 x1) /\ (@FINITE a0 x1).
Definition term156 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((~ (@SUBSET a0 y0 y1)) \/ (~ (@FINITE a0 y1))) \/ (Peano.le (@CARD a0 y0) (@CARD a0 y1)).
Definition term75 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1).
Definition term113 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (forall y0 : nat, ((@HAS_SIZE a0 x0 y0) \/ ((~ (@FINITE a0 x0)) \/ (~ ((@CARD a0 x0) = y0)))) /\ ((~ (@HAS_SIZE a0 x0 y0)) \/ ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0)))).
Definition term112 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (forall y0 : nat, ((fun y1 : nat => (@HAS_SIZE a0 x0 y1) \/ ((~ (@FINITE a0 x0)) \/ (~ ((@CARD a0 x0) = y1)))) y0) /\ ((fun y1 : nat => (~ (@HAS_SIZE a0 x0 y1)) \/ ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y1))) y0)).
Definition term134 (a0 : Type') (x0 : a0 -> Prop) := ((fun y0 : a0 -> Prop => forall y1 : nat, (@HAS_SIZE a0 y0 y1) \/ ((~ (@FINITE a0 y0)) \/ (~ ((@CARD a0 y0) = y1)))) x0) /\ ((fun y0 : a0 -> Prop => forall y1 : nat, (~ (@HAS_SIZE a0 y0 y1)) \/ ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) x0).
Definition term168 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (fun y0 : nat => ((~ (@HAS_SIZE a0 x0 y0)) \/ (@FINITE a0 x0)) /\ ((~ (@HAS_SIZE a0 x0 y0)) \/ ((@CARD a0 x0) = y0))) x1.
Definition term100 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term9 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 y0) -> Peano.le x0 (@CARD a0 y0)) -> exists y1 : a0 -> Prop, (@SUBSET a0 y1 y0) /\ (@HAS_SIZE a0 y1 x0)) x1.
Definition term44 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False.
Definition term38 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := ((@SUBSET a0 x1 x2) -> (@HAS_SIZE a0 x1 x0) -> (@FINITE a0 x2) -> (~ ((Peano.le x0 (@CARD a0 x1)) /\ (Peano.le (@CARD a0 x1) (@CARD a0 x2)))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False) -> (@SUBSET a0 x1 x2) -> (@HAS_SIZE a0 x1 x0) -> (@FINITE a0 x2) -> (~ ((Peano.le x0 (@CARD a0 x1)) /\ (Peano.le (@CARD a0 x1) (@CARD a0 x2)))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False.
Definition term260 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp (~ ((~ (@SUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1)))).
Definition term158 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := ((~ (@HAS_SIZE a0 x0 x1)) \/ (@FINITE a0 x0)) /\ ((~ (@HAS_SIZE a0 x0 x1)) \/ ((@CARD a0 x0) = x1)).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term16 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1) x1.
Definition term265 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : nat, (@SUBSET a0 y0 x0) -> (@HAS_SIZE a0 y0 y1) -> (@FINITE a0 x0) -> (~ ((Peano.le y1 (@CARD a0 y0)) /\ (Peano.le (@CARD a0 y0) (@CARD a0 x0)))) -> (forall y2 : nat, Peano.le y2 y2) -> (forall y2 : a0 -> Prop, forall y3 : nat, (@HAS_SIZE a0 y2 y3) = ((@FINITE a0 y2) /\ ((@CARD a0 y2) = y3))) -> (forall y2 : a0 -> Prop, forall y3 : a0 -> Prop, ((@SUBSET a0 y2 y3) /\ (@FINITE a0 y3)) -> Peano.le (@CARD a0 y2) (@CARD a0 y3)) -> False) x1.
Definition term215 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((Peano.le x1 x3) \/ ((~ (Peano.le x0 x2)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))))).
Definition term146 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) \/ ((~ (@FINITE a0 y0)) \/ (~ ((@CARD a0 y0) = y1)))) /\ (forall y0 : a0 -> Prop, forall y1 : nat, (~ (@HAS_SIZE a0 y0 y1)) \/ ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))).
Definition term217 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) \/ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3)))).
Definition term232 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((x2 = x0) /\ ((x3 = x1) /\ (Peano.le x2 x3))).
Definition term252 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (Peano.le (@CARD a0 x0) (@CARD a0 x1)) \/ ((~ (@SUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1))).
Definition term172 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@SUBSET a0 x0 x1)) \/ ((~ (@FINITE a0 x1)) \/ (Peano.le (@CARD a0 x0) (@CARD a0 x1))).
Definition term236 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := (((@CARD a0 x1) = x0) /\ (((@CARD a0 x1) = (@CARD a0 x1)) /\ (Peano.le (@CARD a0 x1) (@CARD a0 x1)))) -> Peano.le x0 (@CARD a0 x1).
Definition term72 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@SUBSET a0 x0 x1) /\ (@FINITE a0 x1)) -> Peano.le (@CARD a0 x0) (@CARD a0 x1).
Definition term74 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@SUBSET a0 x0 y0) /\ (@FINITE a0 y0)) -> Peano.le (@CARD a0 x0) (@CARD a0 y0).
Definition term166 (x0 : nat) := (fun y0 : nat => Peano.le y0 y0) x0.
Definition term203 (x0 : nat) (x1 : nat) := ~ (Peano.le x0 x1).
Definition term206 (x0 : nat) (x1 : nat) := or (Peano.le x0 x1).
Definition term174 (a0 : Type') (x0 : a0 -> Prop) := ~ (@FINITE a0 x0).
Definition term41 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False.
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term229 (x0 : nat) (x1 : nat) (x2 : nat) := (x2 = x0) /\ (Peano.le x1 x2).
Definition term118 (a0 : Type') (x0 : a0 -> Prop) := and (forall y0 : nat, (@HAS_SIZE a0 x0 y0) \/ ((~ (@FINITE a0 x0)) \/ (~ ((@CARD a0 x0) = y0)))).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term180 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3))).
Definition term176 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le x2 x3) = (Peano.le x0 x1)) -> (Peano.le x0 x1) \/ (~ (Peano.le x2 x3)).
Definition term254 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((~ (@SUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1))).
Definition term144 (a0 : Type') := forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => forall y2 : nat, (~ (@HAS_SIZE a0 y1 y2)) \/ ((@FINITE a0 y1) /\ ((@CARD a0 y1) = y2))) y0.
Definition term139 (a0 : Type') := forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => forall y2 : nat, (@HAS_SIZE a0 y1 y2) \/ ((~ (@FINITE a0 y1)) \/ (~ ((@CARD a0 y1) = y2)))) y0.
Definition term142 (a0 : Type') := and (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) \/ ((~ (@FINITE a0 y0)) \/ (~ ((@CARD a0 y0) = y1)))).
Definition term109 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (fun y0 : nat => (~ (@HAS_SIZE a0 x0 y0)) \/ ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0))) x1.
Definition term119 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : nat => (fun y1 : nat => (~ (@HAS_SIZE a0 x0 y1)) \/ ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y1))) y0.
Definition term114 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : nat => (fun y1 : nat => (@HAS_SIZE a0 x0 y1) \/ ((~ (@FINITE a0 x0)) \/ (~ ((@CARD a0 x0) = y1)))) y0.
Definition term197 (a0 : Type') (x0 : a0 -> Prop) := ~ ((@CARD a0 x0) = (@CARD a0 x0)).
Definition term54 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@FINITE a0 x2) -> (~ ((Peano.le x0 (@CARD a0 x1)) /\ (Peano.le (@CARD a0 x1) (@CARD a0 x2)))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)).
Definition term53 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@FINITE a0 x2) -> (~ ((Peano.le x0 (@CARD a0 x1)) /\ (Peano.le (@CARD a0 x1) (@CARD a0 x2)))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False.
Definition term219 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term274 (a0 : Type') := forall y0 : nat, forall y1 : a0 -> Prop, ((@FINITE a0 y1) -> Peano.le y0 (@CARD a0 y1)) = (exists y2 : a0 -> Prop, (@SUBSET a0 y2 y1) /\ (@HAS_SIZE a0 y2 y0)).
Definition term26 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term15 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term13 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term183 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (~ (@HAS_SIZE a0 x0 x1)) -> @HAS_SIZE a0 x0 x1.
Definition term107 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (fun y0 : nat => (@HAS_SIZE a0 x0 y0) \/ ((~ (@FINITE a0 x0)) \/ (~ ((@CARD a0 x0) = y0)))) x1.
Definition term245 (a0 : Type') (x0 : a0 -> Prop) := or (~ (@FINITE a0 x0)).
Definition term262 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (Peano.le (@CARD a0 x0) (@CARD a0 x1))) -> Peano.le (@CARD a0 x0) (@CARD a0 x1).
Definition term241 (a0 : Type') (x0 : a0 -> Prop) := (~ (@FINITE a0 x0)) -> @FINITE a0 x0.
Definition term234 (a0 : Type') (x0 : a0 -> Prop) := ((@CARD a0 x0) = (@CARD a0 x0)) /\ (Peano.le (@CARD a0 x0) (@CARD a0 x0)).
Definition term132 (a0 : Type') (x0 : a0 -> Prop) := and ((fun y0 : a0 -> Prop => forall y1 : nat, (@HAS_SIZE a0 y0 y1) \/ ((~ (@FINITE a0 y0)) \/ (~ ((@CARD a0 y0) = y1)))) x0).
Definition term185 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := ((@CARD a0 x0) = x1) \/ (~ (@HAS_SIZE a0 x0 x1)).
Definition term148 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@SUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1)).
Definition term55 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := imp (@HAS_SIZE a0 x0 x1).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term171 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (~ (@HAS_SIZE a0 x0 x1)) \/ ((@CARD a0 x0) = x1).
Definition term195 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := ~ ((@CARD a0 x0) = x1).
Definition term88 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := or (@HAS_SIZE a0 x0 x1).
Definition term169 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((~ (@SUBSET a0 y0 y1)) \/ (~ (@FINITE a0 y1))) \/ (Peano.le (@CARD a0 y0) (@CARD a0 y1))) x0.
Definition term167 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : nat, ((~ (@HAS_SIZE a0 y0 y1)) \/ (@FINITE a0 y0)) /\ ((~ (@HAS_SIZE a0 y0 y1)) \/ ((@CARD a0 y0) = y1))) x0.
Definition term133 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : nat, (~ (@HAS_SIZE a0 y0 y1)) \/ ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) x0.
Definition term131 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : nat, (@HAS_SIZE a0 y0 y1) \/ ((~ (@FINITE a0 y0)) \/ (~ ((@CARD a0 y0) = y1)))) x0.
Definition term181 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x2 = x0) -> (~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3))).
Definition term221 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3)))).
Definition term204 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x2 = x0)) \/ (~ (Peano.le x1 x2)).
Definition term127 (a0 : Type') := forall y0 : a0 -> Prop, ((fun y1 : a0 -> Prop => forall y2 : nat, (@HAS_SIZE a0 y1 y2) \/ ((~ (@FINITE a0 y1)) \/ (~ ((@CARD a0 y1) = y2)))) y0) /\ ((fun y1 : a0 -> Prop => forall y2 : nat, (~ (@HAS_SIZE a0 y1 y2)) \/ ((@FINITE a0 y1) /\ ((@CARD a0 y1) = y2))) y0).
Definition term40 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (((@SUBSET a0 x1 x2) -> (@HAS_SIZE a0 x1 x0) -> (@FINITE a0 x2) -> (~ ((Peano.le x0 (@CARD a0 x1)) /\ (Peano.le (@CARD a0 x1) (@CARD a0 x2)))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False) -> (@SUBSET a0 x1 x2) -> (@HAS_SIZE a0 x1 x0) -> (@FINITE a0 x2) -> (~ ((Peano.le x0 (@CARD a0 x1)) /\ (Peano.le (@CARD a0 x1) (@CARD a0 x2)))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False) -> ((@SUBSET a0 x1 x2) -> (@HAS_SIZE a0 x1 x0) -> (@FINITE a0 x2) -> (~ ((Peano.le x0 (@CARD a0 x1)) /\ (Peano.le (@CARD a0 x1) (@CARD a0 x2)))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False) -> (@SUBSET a0 x1 x2) -> (@HAS_SIZE a0 x1 x0) -> (@FINITE a0 x2) -> (~ ((Peano.le x0 (@CARD a0 x1)) /\ (Peano.le (@CARD a0 x1) (@CARD a0 x2)))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False.
Definition term136 (a0 : Type') := @eq Prop (forall y0 : a0 -> Prop, ((fun y1 : a0 -> Prop => forall y2 : nat, (@HAS_SIZE a0 y1 y2) \/ ((~ (@FINITE a0 y1)) \/ (~ ((@CARD a0 y1) = y2)))) y0) /\ ((fun y1 : a0 -> Prop => forall y2 : nat, (~ (@HAS_SIZE a0 y1 y2)) \/ ((@FINITE a0 y1) /\ ((@CARD a0 y1) = y2))) y0)).
Definition term247 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (Peano.le (@CARD a0 x0) (@CARD a0 x1)) \/ ((~ (@FINITE a0 x1)) \/ (~ (@SUBSET a0 x0 x1))).
Definition term178 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x3 = x1) -> (Peano.le x0 x1) \/ (~ (Peano.le x2 x3)).
Definition term91 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := and ((@HAS_SIZE a0 x0 x1) \/ (~ ((@FINITE a0 x0) /\ ((@CARD a0 x0) = x1)))).
Definition term110 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := ((fun y0 : nat => (@HAS_SIZE a0 x0 y0) \/ ((~ (@FINITE a0 x0)) \/ (~ ((@CARD a0 x0) = y0)))) x1) /\ ((fun y0 : nat => (~ (@HAS_SIZE a0 x0 y0)) \/ ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0))) x1).
Definition term102 (x0 : nat -> Prop) (x1 : nat -> Prop) := (forall y0 : nat, x0 y0) /\ (forall y0 : nat, x1 y0).
Definition term76 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) /\ ((@CARD a0 x0) = x1).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term238 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := (Peano.le x0 (@CARD a0 x1)) -> False.
Definition term196 (a0 : Type') (x0 : a0 -> Prop) := (~ ((@CARD a0 x0) = (@CARD a0 x0))) -> (@CARD a0 x0) = (@CARD a0 x0).
Definition term257 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (~ (~ (@SUBSET a0 x0 x1))).
Definition term224 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term17 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term47 (a0 : Type') := (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False.
Definition term235 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := ((@CARD a0 x1) = x0) /\ (((@CARD a0 x1) = (@CARD a0 x1)) /\ (Peano.le (@CARD a0 x1) (@CARD a0 x1))).
Definition term163 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : nat, ((~ (@HAS_SIZE a0 y0 y1)) \/ (@FINITE a0 y0)) /\ ((~ (@HAS_SIZE a0 y0 y1)) \/ ((@CARD a0 y0) = y1)).
Definition term157 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((~ (@SUBSET a0 y0 y1)) \/ (~ (@FINITE a0 y1))) \/ (Peano.le (@CARD a0 y0) (@CARD a0 y1)).
Definition term145 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : nat, (~ (@HAS_SIZE a0 y0 y1)) \/ ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1)).
Definition term140 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) \/ ((~ (@FINITE a0 y0)) \/ (~ ((@CARD a0 y0) = y1))).
Definition term98 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : nat, ((@HAS_SIZE a0 y0 y1) \/ ((~ (@FINITE a0 y0)) \/ (~ ((@CARD a0 y0) = y1)))) /\ ((~ (@HAS_SIZE a0 y0 y1)) \/ ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : nat, (@SUBSET a0 y0 x0) -> (@HAS_SIZE a0 y0 y1) -> (@FINITE a0 x0) -> (~ ((Peano.le y1 (@CARD a0 y0)) /\ (Peano.le (@CARD a0 y0) (@CARD a0 x0)))) -> (forall y2 : nat, Peano.le y2 y2) -> (forall y2 : a0 -> Prop, forall y3 : nat, (@HAS_SIZE a0 y2 y3) = ((@FINITE a0 y2) /\ ((@CARD a0 y2) = y3))) -> ~ (forall y2 : a0 -> Prop, forall y3 : a0 -> Prop, ((@SUBSET a0 y2 y3) /\ (@FINITE a0 y3)) -> Peano.le (@CARD a0 y2) (@CARD a0 y3)).
Definition term66 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : nat, (@SUBSET a0 y0 x0) -> (@HAS_SIZE a0 y0 y1) -> (@FINITE a0 x0) -> (~ ((Peano.le y1 (@CARD a0 y0)) /\ (Peano.le (@CARD a0 y0) (@CARD a0 x0)))) -> (forall y2 : nat, Peano.le y2 y2) -> (forall y2 : a0 -> Prop, forall y3 : nat, (@HAS_SIZE a0 y2 y3) = ((@FINITE a0 y2) /\ ((@CARD a0 y2) = y3))) -> (forall y2 : a0 -> Prop, forall y3 : a0 -> Prop, ((@SUBSET a0 y2 y3) /\ (@FINITE a0 y3)) -> Peano.le (@CARD a0 y2) (@CARD a0 y3)) -> False.
Definition term36 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1)).
Definition term35 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1).
Definition term255 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (~ (@SUBSET a0 x0 x1))) /\ (~ (~ (@FINITE a0 x1))).
Definition term250 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@FINITE a0 x1)) \/ (~ (@SUBSET a0 x0 x1)).
Definition term12 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := (@SUBSET a0 x1 x0) /\ (@HAS_SIZE a0 x1 x2).
Definition term177 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) \/ (~ (Peano.le x2 x3)).
Definition term164 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := ~ (Peano.le x0 (@CARD a0 x1)).
Definition term175 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term122 (a0 : Type') (x0 : a0 -> Prop) := (forall y0 : nat, (@HAS_SIZE a0 x0 y0) \/ ((~ (@FINITE a0 x0)) \/ (~ ((@CARD a0 x0) = y0)))) /\ (forall y0 : nat, (~ (@HAS_SIZE a0 x0 y0)) \/ ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0))).
Definition term233 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x0 = x2) /\ ((x1 = x3) /\ (Peano.le x0 x1))) -> Peano.le x2 x3.
Definition term90 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@HAS_SIZE a0 x0 x1) \/ ((~ (@FINITE a0 x0)) \/ (~ ((@CARD a0 x0) = x1))).
Definition term173 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (@SUBSET a0 x0 x1).
Definition term249 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((Peano.le (@CARD a0 x0) (@CARD a0 x1)) \/ ((~ (@FINITE a0 x1)) \/ (~ (@SUBSET a0 x0 x1)))).
Definition term30 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := (exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 (@CARD a0 x1))) -> Peano.le x0 (@CARD a0 x1).
Definition term121 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : nat, (~ (@HAS_SIZE a0 x0 y0)) \/ ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0)).
Definition term251 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (Peano.le (@CARD a0 x0) (@CARD a0 x1)).
Definition term28 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1) x0.
Definition term230 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x2 = x0) /\ ((x3 = x1) /\ (Peano.le x2 x3)).
Definition term246 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@FINITE a0 x1)) \/ ((Peano.le (@CARD a0 x0) (@CARD a0 x1)) \/ (~ (@SUBSET a0 x0 x1))).
Definition term186 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @eq Prop ((~ (@HAS_SIZE a0 x0 x1)) \/ ((@CARD a0 x0) = x1)).
Definition term123 (a0 : Type') := fun y0 : a0 -> Prop => (forall y1 : nat, (@HAS_SIZE a0 y0 y1) \/ ((~ (@FINITE a0 y0)) \/ (~ ((@CARD a0 y0) = y1)))) /\ (forall y1 : nat, (~ (@HAS_SIZE a0 y0 y1)) \/ ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))).
Definition term125 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := forall y0 : a0 -> Prop, (x0 y0) /\ (x1 y0).
Definition term228 (x0 : nat) (x1 : nat) := ~ (~ (Peano.le x0 x1)).
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term248 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((~ (@SUBSET a0 x0 x1)) \/ ((~ (@FINITE a0 x1)) \/ (Peano.le (@CARD a0 x0) (@CARD a0 x1)))).
Definition term135 (a0 : Type') := fun y0 : a0 -> Prop => ((fun y1 : a0 -> Prop => forall y2 : nat, (@HAS_SIZE a0 y1 y2) \/ ((~ (@FINITE a0 y1)) \/ (~ ((@CARD a0 y1) = y2)))) y0) /\ ((fun y1 : a0 -> Prop => forall y2 : nat, (~ (@HAS_SIZE a0 y1 y2)) \/ ((@FINITE a0 y1) /\ ((@CARD a0 y1) = y2))) y0).
Definition term86 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (~ (@FINITE a0 x0)) \/ (~ ((@CARD a0 x0) = x1)).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := exists y0 : a0 -> Prop, (@SUBSET a0 y0 x0) /\ (@HAS_SIZE a0 y0 x1).
Definition term216 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3))).
Definition term211 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x1 = x0)) \/ ((~ (Peano.le x1 x2)) \/ (~ (x2 = x3))).
Definition term32 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (Peano.le x0 (@CARD a0 x1)) /\ (Peano.le (@CARD a0 x1) (@CARD a0 x2)).
Definition term78 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : nat, (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0)).
Definition term226 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((~ (x2 = x0)) \/ (~ (Peano.le x1 x2))).
Definition term214 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq Prop ((~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3))))).
Definition term128 (a0 : Type') := (forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => forall y2 : nat, (@HAS_SIZE a0 y1 y2) \/ ((~ (@FINITE a0 y1)) \/ (~ ((@CARD a0 y1) = y2)))) y0) /\ (forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => forall y2 : nat, (~ (@HAS_SIZE a0 y1 y2)) \/ ((@FINITE a0 y1) /\ ((@CARD a0 y1) = y2))) y0).
Definition term81 := forall y0 : nat, Peano.le y0 y0.
Definition term24 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1)) -> Peano.le x0 x1.
Definition term261 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp ((@SUBSET a0 x0 x1) /\ (@FINITE a0 x1)).
Definition term45 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)).
Definition term106 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : nat => (~ (@HAS_SIZE a0 x0 y0)) \/ ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0)).
Definition term117 (a0 : Type') (x0 : a0 -> Prop) := and (forall y0 : nat, (fun y1 : nat => (@HAS_SIZE a0 x0 y1) \/ ((~ (@FINITE a0 x0)) \/ (~ ((@CARD a0 x0) = y1)))) y0).
Definition term259 (a0 : Type') (x0 : a0 -> Prop) := ~ (~ (@FINITE a0 x0)).
Definition term179 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term222 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (~ (x2 = x0))) /\ (~ ((~ (x3 = x1)) \/ (~ (Peano.le x2 x3)))).
Definition term271 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := (exists y0 : a0 -> Prop, (@SUBSET a0 y0 x1) /\ (@HAS_SIZE a0 y0 x0)) -> (@FINITE a0 x1) -> Peano.le x0 (@CARD a0 x1).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term93 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := ((@HAS_SIZE a0 x0 x1) \/ (~ ((@FINITE a0 x0) /\ ((@CARD a0 x0) = x1)))) /\ ((~ (@HAS_SIZE a0 x0 x1)) \/ ((@FINITE a0 x0) /\ ((@CARD a0 x0) = x1))).
Definition term263 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (Peano.le (@CARD a0 x0) (@CARD a0 x1)) -> False.
Definition term212 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.le x0 x2)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3))).
Definition term77 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : nat => (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0)).
Definition term23 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term48 (a0 : Type') := (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)).
Definition term141 (a0 : Type') := and (forall y0 : a0 -> Prop, (fun y1 : a0 -> Prop => forall y2 : nat, (@HAS_SIZE a0 y1 y2) \/ ((~ (@FINITE a0 y1)) \/ (~ ((@CARD a0 y1) = y2)))) y0).
Definition term99 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term89 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@HAS_SIZE a0 x0 x1) \/ (~ ((@FINITE a0 x0) /\ ((@CARD a0 x0) = x1))).
Definition term213 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x1 x3) \/ ((~ (Peano.le x0 x2)) \/ ((~ (x0 = x1)) \/ (~ (x2 = x3)))).
Definition term69 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : nat, (@SUBSET a0 y1 y0) -> (@HAS_SIZE a0 y1 y2) -> (@FINITE a0 y0) -> (~ ((Peano.le y2 (@CARD a0 y1)) /\ (Peano.le (@CARD a0 y1) (@CARD a0 y0)))) -> (forall y3 : nat, Peano.le y3 y3) -> (forall y3 : a0 -> Prop, forall y4 : nat, (@HAS_SIZE a0 y3 y4) = ((@FINITE a0 y3) /\ ((@CARD a0 y3) = y4))) -> ~ (forall y3 : a0 -> Prop, forall y4 : a0 -> Prop, ((@SUBSET a0 y3 y4) /\ (@FINITE a0 y4)) -> Peano.le (@CARD a0 y3) (@CARD a0 y4)).
Definition term68 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : nat, (@SUBSET a0 y1 y0) -> (@HAS_SIZE a0 y1 y2) -> (@FINITE a0 y0) -> (~ ((Peano.le y2 (@CARD a0 y1)) /\ (Peano.le (@CARD a0 y1) (@CARD a0 y0)))) -> (forall y3 : nat, Peano.le y3 y3) -> (forall y3 : a0 -> Prop, forall y4 : nat, (@HAS_SIZE a0 y3 y4) = ((@FINITE a0 y3) /\ ((@CARD a0 y3) = y4))) -> (forall y3 : a0 -> Prop, forall y4 : a0 -> Prop, ((@SUBSET a0 y3 y4) /\ (@FINITE a0 y4)) -> Peano.le (@CARD a0 y3) (@CARD a0 y4)) -> False.
Definition term266 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : nat) := (fun y0 : nat => (@SUBSET a0 x0 x1) -> (@HAS_SIZE a0 x0 y0) -> (@FINITE a0 x1) -> (~ ((Peano.le y0 (@CARD a0 x0)) /\ (Peano.le (@CARD a0 x0) (@CARD a0 x1)))) -> (forall y1 : nat, Peano.le y1 y1) -> (forall y1 : a0 -> Prop, forall y2 : nat, (@HAS_SIZE a0 y1 y2) = ((@FINITE a0 y1) /\ ((@CARD a0 y1) = y2))) -> (forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, ((@SUBSET a0 y1 y2) /\ (@FINITE a0 y2)) -> Peano.le (@CARD a0 y1) (@CARD a0 y2)) -> False) x2.
Definition term108 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := and ((fun y0 : nat => (@HAS_SIZE a0 x0 y0) \/ ((~ (@FINITE a0 x0)) \/ (~ ((@CARD a0 x0) = y0)))) x1).
Definition term137 (a0 : Type') := @eq Prop (forall y0 : a0 -> Prop, (forall y1 : nat, (@HAS_SIZE a0 y0 y1) \/ ((~ (@FINITE a0 y0)) \/ (~ ((@CARD a0 y0) = y1)))) /\ (forall y1 : nat, (~ (@HAS_SIZE a0 y0 y1)) \/ ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1)))).
Definition term162 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : nat, ((~ (@HAS_SIZE a0 y0 y1)) \/ (@FINITE a0 y0)) /\ ((~ (@HAS_SIZE a0 y0 y1)) \/ ((@CARD a0 y0) = y1)).
Definition term130 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : nat, (~ (@HAS_SIZE a0 y0 y1)) \/ ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1)).
Definition term129 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : nat, (@HAS_SIZE a0 y0 y1) \/ ((~ (@FINITE a0 y0)) \/ (~ ((@CARD a0 y0) = y1))).
Definition term97 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : nat, ((@HAS_SIZE a0 y0 y1) \/ ((~ (@FINITE a0 y0)) \/ (~ ((@CARD a0 y0) = y1)))) /\ ((~ (@HAS_SIZE a0 y0 y1)) \/ ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))).
Definition term79 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1)).
Definition term65 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : nat, (@SUBSET a0 y0 x0) -> (@HAS_SIZE a0 y0 y1) -> (@FINITE a0 x0) -> (~ ((Peano.le y1 (@CARD a0 y0)) /\ (Peano.le (@CARD a0 y0) (@CARD a0 x0)))) -> (forall y2 : nat, Peano.le y2 y2) -> (forall y2 : a0 -> Prop, forall y3 : nat, (@HAS_SIZE a0 y2 y3) = ((@FINITE a0 y2) /\ ((@CARD a0 y2) = y3))) -> ~ (forall y2 : a0 -> Prop, forall y3 : a0 -> Prop, ((@SUBSET a0 y2 y3) /\ (@FINITE a0 y3)) -> Peano.le (@CARD a0 y2) (@CARD a0 y3)).
Definition term64 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : nat, (@SUBSET a0 y0 x0) -> (@HAS_SIZE a0 y0 y1) -> (@FINITE a0 x0) -> (~ ((Peano.le y1 (@CARD a0 y0)) /\ (Peano.le (@CARD a0 y0) (@CARD a0 x0)))) -> (forall y2 : nat, Peano.le y2 y2) -> (forall y2 : a0 -> Prop, forall y3 : nat, (@HAS_SIZE a0 y2 y3) = ((@FINITE a0 y2) /\ ((@CARD a0 y2) = y3))) -> (forall y2 : a0 -> Prop, forall y3 : a0 -> Prop, ((@SUBSET a0 y2 y3) /\ (@FINITE a0 y3)) -> Peano.le (@CARD a0 y2) (@CARD a0 y3)) -> False.
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term187 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @eq Prop (((@CARD a0 x0) = x1) \/ (~ (@HAS_SIZE a0 x0 x1))).
Definition term73 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((@SUBSET a0 x0 y0) /\ (@FINITE a0 y0)) -> Peano.le (@CARD a0 x0) (@CARD a0 y0).
Definition term155 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((~ (@SUBSET a0 x0 y0)) \/ (~ (@FINITE a0 y0))) \/ (Peano.le (@CARD a0 x0) (@CARD a0 y0)).
Definition term34 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := ~ ((Peano.le x0 (@CARD a0 x1)) /\ (Peano.le (@CARD a0 x1) (@CARD a0 x2))).
Definition term223 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term269 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> Peano.le x0 (@CARD a0 x1).
Definition term160 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : nat => ((~ (@HAS_SIZE a0 x0 y0)) \/ (@FINITE a0 x0)) /\ ((~ (@HAS_SIZE a0 x0 y0)) \/ ((@CARD a0 x0) = y0)).
Definition term208 (x0 : nat) (x1 : nat) := or (~ (x0 = x1)).
Definition term82 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (~ (Peano.le x0 (@CARD a0 x1))) \/ (~ (Peano.le (@CARD a0 x1) (@CARD a0 x2))).
Definition term256 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ (@SUBSET a0 x0 x1)).
Definition term182 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((Peano.le x0 x1) \/ (~ (Peano.le x2 x3)))).
Definition term50 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (~ ((Peano.le x0 (@CARD a0 x1)) /\ (Peano.le (@CARD a0 x1) (@CARD a0 x2)))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) -> False.
Definition term87 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (~ (@HAS_SIZE a0 x0 x1)) \/ ((@FINITE a0 x0) /\ ((@CARD a0 x0) = x1)).
Definition term170 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((~ (@SUBSET a0 x0 y0)) \/ (~ (@FINITE a0 y0))) \/ (Peano.le (@CARD a0 x0) (@CARD a0 y0))) x1.
Definition term51 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (~ ((Peano.le x0 (@CARD a0 x1)) /\ (Peano.le (@CARD a0 x1) (@CARD a0 x2)))) -> (forall y0 : nat, Peano.le y0 y0) -> (forall y0 : a0 -> Prop, forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) -> ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)).
Definition term126 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := (forall y0 : a0 -> Prop, x0 y0) /\ (forall y0 : a0 -> Prop, x1 y0).
Definition term84 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := Peano.le (@CARD a0 x0) (@CARD a0 x1).
Definition term242 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@FINITE a0 x1)) \/ ((~ (@SUBSET a0 x0 x1)) \/ (Peano.le (@CARD a0 x0) (@CARD a0 x1))).
Definition term272 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := (((@FINITE a0 x1) -> Peano.le x0 (@CARD a0 x1)) -> exists y0 : a0 -> Prop, (@SUBSET a0 y0 x1) /\ (@HAS_SIZE a0 y0 x0)) /\ ((exists y0 : a0 -> Prop, (@SUBSET a0 y0 x1) /\ (@HAS_SIZE a0 y0 x0)) -> (@FINITE a0 x1) -> Peano.le x0 (@CARD a0 x1)).
Definition term96 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : nat, ((@HAS_SIZE a0 x0 y0) \/ ((~ (@FINITE a0 x0)) \/ (~ ((@CARD a0 x0) = y0)))) /\ ((~ (@HAS_SIZE a0 x0 y0)) \/ ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0))).
Definition term267 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 (@CARD a0 x1)).
Definition term150 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or ((~ (@SUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1))).
Definition term253 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ ((~ (@SUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1)))) -> Peano.le (@CARD a0 x0) (@CARD a0 x1).
Definition term193 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@HAS_SIZE a0 x0 x1) -> (@CARD a0 x0) = x1.
Definition term29 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0) x1.
Definition term192 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := imp (~ (~ (@HAS_SIZE a0 x0 x1))).
