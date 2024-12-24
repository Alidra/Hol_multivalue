Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term90 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((~ (@SUBSET a0 x0 y0)) \/ ((@CARD a0 x0) = (@CARD a0 y0))) \/ (@PSUBSET a0 x0 y0).
Definition term152 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term165 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp (~ ((~ (x3 = x1)) \/ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3))))).
Definition term144 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@SUBSET a0 x0 x1)) -> @SUBSET a0 x0 x1.
Definition term84 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (~ ((@SUBSET a0 x0 x1) /\ (~ ((@CARD a0 x0) = (@CARD a0 x1))))).
Definition term52 (a0 : Type') (x0 : type686 a0) := ~ (all x0).
Definition term135 := (~ False) -> False.
Definition term81 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@SUBSET a0 x0 x1)) \/ ((@CARD a0 x0) = (@CARD a0 x1)).
Definition term189 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp (~ ((~ (@SUBSET a0 x0 x1)) \/ ((@CARD a0 x0) = (@CARD a0 x1)))).
Definition term188 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (@SUBSET a0 x0 x1).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((@PSUBSET a0 x0 x1) /\ (@FINITE a0 x1)).
Definition term126 (x0 : Prop) := ~ (~ x0).
Definition term71 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ ((@PSUBSET a0 x0 x1) /\ (@FINITE a0 x1))) \/ (Peano.lt (@CARD a0 x0) (@CARD a0 x1)).
Definition term121 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ ((~ (@PSUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1)))) -> Peano.lt (@CARD a0 x0) (@CARD a0 x1).
Definition term59 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) /\ (((@PSUBSET a0 x0 y0) /\ (~ (Peano.lt (@CARD a0 x0) (@CARD a0 y0)))) \/ ((~ (@PSUBSET a0 x0 y0)) /\ (Peano.lt (@CARD a0 x0) (@CARD a0 y0)))).
Definition term13 (a0 : Type') (a1 : Type') := (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> (@PSUBSET a0 y0 y1) = (Peano.lt (@CARD a0 y0) (@CARD a0 y1)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@PSUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.lt (@CARD a0 y0) (@CARD a0 y1)) -> (forall y0 : a1 -> Prop, forall y1 : a1 -> Prop, ((@PSUBSET a1 y0 y1) /\ (@FINITE a1 y1)) -> Peano.lt (@CARD a1 y0) (@CARD a1 y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> @PSUBSET a0 y0 y1) -> False.
Definition term101 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (@PSUBSET a0 x0 x1).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (((@FINITE a0 x1) /\ (@SUBSET a0 x0 x1)) -> (@PSUBSET a0 x0 x1) = (Peano.lt (@CARD a0 x0) (@CARD a0 x1))).
Definition term133 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (Peano.lt (@CARD a0 x0) (@CARD a0 x1))) -> Peano.lt (@CARD a0 x0) (@CARD a0 x1).
Definition term178 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop (((@CARD a0 x0) = (@CARD a0 x1)) \/ ((@PSUBSET a0 x0 x1) \/ (~ (@SUBSET a0 x0 x1)))).
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x1) /\ (@SUBSET a0 x0 x1)) -> (@PSUBSET a0 x0 x1) = (Peano.lt (@CARD a0 x0) (@CARD a0 x1)).
Definition term23 (a0 : Type') (a1 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@PSUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.lt (@CARD a0 y0) (@CARD a0 y1)) -> (forall y0 : a1 -> Prop, forall y1 : a1 -> Prop, ((@PSUBSET a1 y0 y1) /\ (@FINITE a1 y1)) -> Peano.lt (@CARD a1 y0) (@CARD a1 y1)) -> ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> @PSUBSET a0 y0 y1).
Definition term184 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((~ (@SUBSET a0 x0 x1)) \/ ((@CARD a0 x0) = (@CARD a0 x1))).
Definition term3 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0).
Definition term7 (x0 : Prop) := (~ x0) -> False.
Definition term153 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((~ (x3 = x1)) \/ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3)))).
Definition term47 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and ((@FINITE a0 x1) /\ (@SUBSET a0 x0 x1)).
Definition term110 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@PSUBSET a0 x0 x1)) \/ (Peano.lt (@CARD a0 x0) (@CARD a0 x1)).
Definition term182 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@PSUBSET a0 x0 x1) \/ (((@CARD a0 x0) = (@CARD a0 x1)) \/ (~ (@SUBSET a0 x0 x1))).
Definition term103 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (Peano.lt (@CARD a0 x0) (@CARD a0 x1)).
Definition term72 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((~ (@PSUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1))) \/ (Peano.lt (@CARD a0 x0) (@CARD a0 x1)).
Definition term104 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@SUBSET a0 x0 x1)) \/ (((@CARD a0 x0) = (@CARD a0 x1)) \/ (@PSUBSET a0 x0 x1)).
Definition term44 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((@PSUBSET a0 x0 x1) = (Peano.lt (@CARD a0 x0) (@CARD a0 x1))).
Definition term120 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term157 (x0 : nat) (x1 : nat) := and (x0 = x1).
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x1) /\ (@SUBSET a0 x0 x1)) /\ (~ ((@PSUBSET a0 x0 x1) = (Peano.lt (@CARD a0 x0) (@CARD a0 x1)))).
Definition term69 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (~ ((@PSUBSET a0 x0 x1) /\ (@FINITE a0 x1))).
Definition term86 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ ((@SUBSET a0 x0 x1) /\ (~ ((@CARD a0 x0) = (@CARD a0 x1))))) \/ (@PSUBSET a0 x0 x1).
Definition term106 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@PSUBSET a0 x0 x1)) -> @PSUBSET a0 x0 x1.
Definition term83 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((@CARD a0 x0) = (@CARD a0 x1)).
Definition term19 (a0 : Type') := imp (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@PSUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.lt (@CARD a0 y0) (@CARD a0 y1)).
Definition term18 (a0 : Type') := ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> @PSUBSET a0 y0 y1).
Definition term10 (a0 : Type') := ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> (@PSUBSET a0 y0 y1) = (Peano.lt (@CARD a0 y0) (@CARD a0 y1))).
Definition term85 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or ((~ (@SUBSET a0 x0 x1)) \/ ((@CARD a0 x0) = (@CARD a0 x1))).
Definition term107 (x0 : Prop) := (~ x0) -> x0.
Definition term64 (a0 : Type') := fun y0 : a0 -> Prop => ~ ((fun y1 : a0 -> Prop => forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (@SUBSET a0 y1 y2)) -> (@PSUBSET a0 y1 y2) = (Peano.lt (@CARD a0 y1) (@CARD a0 y2))) y0).
Definition term45 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@PSUBSET a0 x0 x1) /\ (~ (Peano.lt (@CARD a0 x0) (@CARD a0 x1)))) \/ ((~ (@PSUBSET a0 x0 x1)) /\ (Peano.lt (@CARD a0 x0) (@CARD a0 x1))).
Definition term94 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@PSUBSET a0 x0 x1)) /\ (Peano.lt (@CARD a0 x0) (@CARD a0 x1)).
Definition term123 (x0 : Prop) (x1 : Prop) := (~ x0) /\ (~ x1).
Definition term78 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ ((@CARD a0 x0) = (@CARD a0 x1))).
Definition term42 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> (@PSUBSET a0 x0 y0) = (Peano.lt (@CARD a0 x0) (@CARD a0 y0)).
Definition term76 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((~ (@PSUBSET a0 y0 y1)) \/ (~ (@FINITE a0 y1))) \/ (Peano.lt (@CARD a0 y0) (@CARD a0 y1)).
Definition term43 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> (@PSUBSET a0 y0 y1) = (Peano.lt (@CARD a0 y0) (@CARD a0 y1)).
Definition term36 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@PSUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.lt (@CARD a0 y0) (@CARD a0 y1).
Definition term22 (a0 : Type') (a1 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@PSUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.lt (@CARD a0 y0) (@CARD a0 y1)) -> (forall y0 : a1 -> Prop, forall y1 : a1 -> Prop, ((@PSUBSET a1 y0 y1) /\ (@FINITE a1 y1)) -> Peano.lt (@CARD a1 y0) (@CARD a1 y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> @PSUBSET a0 y0 y1) -> False.
Definition term166 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((x3 = x1) /\ ((~ (Peano.lt x0 x1)) /\ (Peano.lt x2 x3))).
Definition term82 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((@SUBSET a0 x0 x1) /\ (~ ((@CARD a0 x0) = (@CARD a0 x1)))).
Definition term154 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (~ (x3 = x1))) /\ (~ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3)))).
Definition term20 (a0 : Type') (a1 : Type') := (forall y0 : a1 -> Prop, forall y1 : a1 -> Prop, ((@PSUBSET a1 y0 y1) /\ (@FINITE a1 y1)) -> Peano.lt (@CARD a1 y0) (@CARD a1 y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> @PSUBSET a0 y0 y1) -> False.
Definition term111 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (Peano.lt (@CARD a0 x0) (@CARD a0 x1)) \/ (~ (@PSUBSET a0 x0 x1)).
Definition term131 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp (~ ((~ (@PSUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1)))).
Definition term185 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (~ (@SUBSET a0 x0 x1))) /\ (~ ((@CARD a0 x0) = (@CARD a0 x1))).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 \/ (x1 \/ x2).
Definition term158 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3))).
Definition term161 (x0 : nat) (x1 : nat) := ~ (~ (Peano.lt x0 x1)).
Definition term117 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@FINITE a0 x1)) \/ (~ (@PSUBSET a0 x0 x1)).
Definition term191 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@PSUBSET a0 x0 x1) -> False.
Definition term138 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3)).
Definition term147 (a0 : Type') (x0 : a0 -> Prop) := ~ (Peano.lt (@CARD a0 x0) (@CARD a0 x0)).
Definition term162 (x0 : nat) (x1 : nat) := and (~ (Peano.lt x0 x1)).
Definition term35 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@PSUBSET a0 x0 y0) /\ (@FINITE a0 y0)) -> Peano.lt (@CARD a0 x0) (@CARD a0 y0).
Definition term79 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (~ (@SUBSET a0 x0 x1)).
Definition term102 (a0 : Type') (x0 : a0 -> Prop) := ~ (@FINITE a0 x0).
Definition term109 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@FINITE a0 x1)) \/ ((~ (@PSUBSET a0 x0 x1)) \/ (Peano.lt (@CARD a0 x0) (@CARD a0 x1))).
Definition term63 (a0 : Type') (x0 : a0 -> Prop) := ~ ((fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> (@PSUBSET a0 y0 y1) = (Peano.lt (@CARD a0 y0) (@CARD a0 y1))) x0).
Definition term17 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> @PSUBSET a0 y0 y1) -> False.
Definition term177 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((~ (@SUBSET a0 x0 x1)) \/ (((@CARD a0 x0) = (@CARD a0 x1)) \/ (@PSUBSET a0 x0 x1))).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x1) /\ (@SUBSET a0 x0 x1)) /\ (((@PSUBSET a0 x0 x1) /\ (~ (Peano.lt (@CARD a0 x0) (@CARD a0 x1)))) \/ ((~ (@PSUBSET a0 x0 x1)) /\ (Peano.lt (@CARD a0 x0) (@CARD a0 x1)))).
Definition term54 (a0 : Type') (x0 : a0 -> Prop) := ~ (forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> (@PSUBSET a0 x0 y0) = (Peano.lt (@CARD a0 x0) (@CARD a0 y0))).
Definition term16 (a0 : Type') (a1 : Type') := (((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> (@PSUBSET a0 y0 y1) = (Peano.lt (@CARD a0 y0) (@CARD a0 y1)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@PSUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.lt (@CARD a0 y0) (@CARD a0 y1)) -> (forall y0 : a1 -> Prop, forall y1 : a1 -> Prop, ((@PSUBSET a1 y0 y1) /\ (@FINITE a1 y1)) -> Peano.lt (@CARD a1 y0) (@CARD a1 y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> @PSUBSET a0 y0 y1) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> (@PSUBSET a0 y0 y1) = (Peano.lt (@CARD a0 y0) (@CARD a0 y1)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@PSUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.lt (@CARD a0 y0) (@CARD a0 y1)) -> (forall y0 : a1 -> Prop, forall y1 : a1 -> Prop, ((@PSUBSET a1 y0 y1) /\ (@FINITE a1 y1)) -> Peano.lt (@CARD a1 y0) (@CARD a1 y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> @PSUBSET a0 y0 y1) -> False) -> ((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> (@PSUBSET a0 y0 y1) = (Peano.lt (@CARD a0 y0) (@CARD a0 y1)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@PSUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.lt (@CARD a0 y0) (@CARD a0 y1)) -> (forall y0 : a1 -> Prop, forall y1 : a1 -> Prop, ((@PSUBSET a1 y0 y1) /\ (@FINITE a1 y1)) -> Peano.lt (@CARD a1 y0) (@CARD a1 y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> @PSUBSET a0 y0 y1) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> (@PSUBSET a0 y0 y1) = (Peano.lt (@CARD a0 y0) (@CARD a0 y1)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@PSUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.lt (@CARD a0 y0) (@CARD a0 y1)) -> (forall y0 : a1 -> Prop, forall y1 : a1 -> Prop, ((@PSUBSET a1 y0 y1) /\ (@FINITE a1 y1)) -> Peano.lt (@CARD a1 y0) (@CARD a1 y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> @PSUBSET a0 y0 y1) -> False.
Definition term24 := imp (forall y0 : nat, ~ (Peano.lt y0 y0)).
Definition term61 (a0 : Type') := exists y0 : a0 -> Prop, ~ ((fun y1 : a0 -> Prop => forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (@SUBSET a0 y1 y2)) -> (@PSUBSET a0 y1 y2) = (Peano.lt (@CARD a0 y1) (@CARD a0 y2))) y0).
Definition term55 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0 -> Prop, ~ ((fun y1 : a0 -> Prop => ((@FINITE a0 y1) /\ (@SUBSET a0 x0 y1)) -> (@PSUBSET a0 x0 y1) = (Peano.lt (@CARD a0 x0) (@CARD a0 y1))) y0).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, forall y2 : Prop, (y0 \/ (y1 \/ y2)) = ((y0 \/ y1) \/ y2)) x0.
Definition term141 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x3 = x1)) \/ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3))).
Definition term73 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@PSUBSET a0 x0 x1) /\ (@FINITE a0 x1).
Definition term137 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.lt x2 x3) = (Peano.lt x0 x1)) -> (Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3)).
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x1) /\ (@SUBSET a0 x0 x1).
Definition term124 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((~ (@PSUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1))).
Definition term146 (a0 : Type') (x0 : a0 -> Prop) := ~ ((@CARD a0 x0) = (@CARD a0 x0)).
Definition term122 (x0 : Prop) (x1 : Prop) := ~ (x0 \/ x1).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@PSUBSET a0 x0 x1) /\ (@FINITE a0 x1)) -> Peano.lt (@CARD a0 x0) (@CARD a0 x1).
Definition term171 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@CARD a0 x0) = (@CARD a0 x1)) -> ~ ((@CARD a0 x0) = (@CARD a0 x1)).
Definition term58 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ~ ((fun y1 : a0 -> Prop => ((@FINITE a0 y1) /\ (@SUBSET a0 x0 y1)) -> (@PSUBSET a0 x0 y1) = (Peano.lt (@CARD a0 x0) (@CARD a0 y1))) y0).
Definition term148 (a0 : Type') (x0 : a0 -> Prop) := (Peano.lt (@CARD a0 x0) (@CARD a0 x0)) -> ~ (Peano.lt (@CARD a0 x0) (@CARD a0 x0)).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((@PSUBSET a0 x0 y0) /\ (@FINITE a0 y0)) -> Peano.lt (@CARD a0 x0) (@CARD a0 y0).
Definition term119 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (Peano.lt (@CARD a0 x0) (@CARD a0 x1)) \/ ((~ (@PSUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1))).
Definition term112 (a0 : Type') (x0 : a0 -> Prop) := or (~ (@FINITE a0 x0)).
Definition term108 (a0 : Type') (x0 : a0 -> Prop) := (~ (@FINITE a0 x0)) -> @FINITE a0 x0.
Definition term163 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.lt x0 x1)) /\ (Peano.lt x2 x3).
Definition term93 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@PSUBSET a0 x0 x1) /\ (~ (Peano.lt (@CARD a0 x0) (@CARD a0 x1))).
Definition term168 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (Peano.lt (@CARD a0 x1) (@CARD a0 x1))) /\ (Peano.lt (@CARD a0 x0) (@CARD a0 x1)).
Definition term60 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) /\ (((@PSUBSET a0 x0 y0) /\ (~ (Peano.lt (@CARD a0 x0) (@CARD a0 y0)))) \/ ((~ (@PSUBSET a0 x0 y0)) /\ (Peano.lt (@CARD a0 x0) (@CARD a0 y0)))).
Definition term15 (a0 : Type') (a1 : Type') := (((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> (@PSUBSET a0 y0 y1) = (Peano.lt (@CARD a0 y0) (@CARD a0 y1)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@PSUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.lt (@CARD a0 y0) (@CARD a0 y1)) -> (forall y0 : a1 -> Prop, forall y1 : a1 -> Prop, ((@PSUBSET a1 y0 y1) /\ (@FINITE a1 y1)) -> Peano.lt (@CARD a1 y0) (@CARD a1 y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> @PSUBSET a0 y0 y1) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> (@PSUBSET a0 y0 y1) = (Peano.lt (@CARD a0 y0) (@CARD a0 y1)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@PSUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.lt (@CARD a0 y0) (@CARD a0 y1)) -> (forall y0 : a1 -> Prop, forall y1 : a1 -> Prop, ((@PSUBSET a1 y0 y1) /\ (@FINITE a1 y1)) -> Peano.lt (@CARD a1 y0) (@CARD a1 y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> @PSUBSET a0 y0 y1) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> (@PSUBSET a0 y0 y1) = (Peano.lt (@CARD a0 y0) (@CARD a0 y1)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@PSUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.lt (@CARD a0 y0) (@CARD a0 y1)) -> (forall y0 : a1 -> Prop, forall y1 : a1 -> Prop, ((@PSUBSET a1 y0 y1) /\ (@FINITE a1 y1)) -> Peano.lt (@CARD a1 y0) (@CARD a1 y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> @PSUBSET a0 y0 y1) -> False.
Definition term170 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((@CARD a0 x1) = (@CARD a0 x1)) /\ ((~ (Peano.lt (@CARD a0 x1) (@CARD a0 x1))) /\ (Peano.lt (@CARD a0 x0) (@CARD a0 x1)))) -> ~ ((@CARD a0 x0) = (@CARD a0 x1)).
Definition term68 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@PSUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1)).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 \/ x1) \/ x2.
Definition term98 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((~ (@SUBSET a0 y0 y1)) \/ ((@CARD a0 y0) = (@CARD a0 y1))) \/ (@PSUBSET a0 y0 y1)) x0.
Definition term95 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((~ (@PSUBSET a0 y0 y1)) \/ (~ (@FINITE a0 y1))) \/ (Peano.lt (@CARD a0 y0) (@CARD a0 y1))) x0.
Definition term62 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> (@PSUBSET a0 y0 y1) = (Peano.lt (@CARD a0 y0) (@CARD a0 y1))) x0.
Definition term142 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x2 = x0) -> (~ (x3 = x1)) \/ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3))).
Definition term14 (a0 : Type') (a1 : Type') := ((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> (@PSUBSET a0 y0 y1) = (Peano.lt (@CARD a0 y0) (@CARD a0 y1)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@PSUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.lt (@CARD a0 y0) (@CARD a0 y1)) -> (forall y0 : a1 -> Prop, forall y1 : a1 -> Prop, ((@PSUBSET a1 y0 y1) /\ (@FINITE a1 y1)) -> Peano.lt (@CARD a1 y0) (@CARD a1 y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> @PSUBSET a0 y0 y1) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> (@PSUBSET a0 y0 y1) = (Peano.lt (@CARD a0 y0) (@CARD a0 y1)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@PSUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.lt (@CARD a0 y0) (@CARD a0 y1)) -> (forall y0 : a1 -> Prop, forall y1 : a1 -> Prop, ((@PSUBSET a1 y0 y1) /\ (@FINITE a1 y1)) -> Peano.lt (@CARD a1 y0) (@CARD a1 y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> @PSUBSET a0 y0 y1) -> False.
Definition term56 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> (@PSUBSET a0 x0 y0) = (Peano.lt (@CARD a0 x0) (@CARD a0 y0))) x1.
Definition term37 (x0 : nat) := ~ (Peano.lt x0 x0).
Definition term9 (a0 : Type') := (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> (@PSUBSET a0 y0 y1) = (Peano.lt (@CARD a0 y0) (@CARD a0 y1)))) -> False.
Definition term39 := forall y0 : nat, ~ (Peano.lt y0 y0).
Definition term139 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x3 = x1) -> (Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3)).
Definition term29 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@SUBSET a0 x0 x1) /\ (~ ((@CARD a0 x0) = (@CARD a0 x1)))) -> @PSUBSET a0 x0 x1.
Definition term41 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> (@PSUBSET a0 x0 y0) = (Peano.lt (@CARD a0 x0) (@CARD a0 y0)).
Definition term175 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or ((@CARD a0 x0) = (@CARD a0 x1)).
Definition term1 (x0 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1).
Definition term38 := fun y0 : nat => ~ (Peano.lt y0 y0).
Definition term145 (a0 : Type') (x0 : a0 -> Prop) := (~ ((@CARD a0 x0) = (@CARD a0 x0))) -> (@CARD a0 x0) = (@CARD a0 x0).
Definition term187 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (~ (~ (@SUBSET a0 x0 x1))).
Definition term156 (x0 : nat) (x1 : nat) := and (~ (~ (x0 = x1))).
Definition term128 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (~ (~ (@PSUBSET a0 x0 x1))).
Definition term190 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp ((@SUBSET a0 x0 x1) /\ (~ ((@CARD a0 x0) = (@CARD a0 x1)))).
Definition term92 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((~ (@SUBSET a0 y0 y1)) \/ ((@CARD a0 y0) = (@CARD a0 y1))) \/ (@PSUBSET a0 y0 y1).
Definition term77 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((~ (@PSUBSET a0 y0 y1)) \/ (~ (@FINITE a0 y1))) \/ (Peano.lt (@CARD a0 y0) (@CARD a0 y1)).
Definition term12 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@PSUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.lt (@CARD a0 y0) (@CARD a0 y1).
Definition term11 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> @PSUBSET a0 y0 y1.
Definition term8 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> (@PSUBSET a0 y0 y1) = (Peano.lt (@CARD a0 y0) (@CARD a0 y1)).
Definition term183 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ ((~ (@SUBSET a0 x0 x1)) \/ ((@CARD a0 x0) = (@CARD a0 x1)))) -> @PSUBSET a0 x0 x1.
Definition term167 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x1 = x0) /\ ((~ (Peano.lt x3 x0)) /\ (Peano.lt x2 x1))) -> ~ (x2 = x3).
Definition term53 (a0 : Type') (x0 : type686 a0) := exists y0 : a0 -> Prop, ~ (x0 y0).
Definition term125 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (~ (@PSUBSET a0 x0 x1))) /\ (~ (~ (@FINITE a0 x1))).
Definition term180 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (@PSUBSET a0 x0 x1).
Definition term136 (x0 : Prop) (x1 : Prop) := (x1 = x0) -> x0 \/ (~ x1).
Definition term174 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@PSUBSET a0 x0 x1) \/ (~ (@SUBSET a0 x0 x1)).
Definition term89 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((~ (@SUBSET a0 x0 y0)) \/ ((@CARD a0 x0) = (@CARD a0 y0))) \/ (@PSUBSET a0 x0 y0).
Definition term105 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (@SUBSET a0 x0 x1).
Definition term160 (x0 : nat) (x1 : nat) := ~ (Peano.lt x0 x1).
Definition term116 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((Peano.lt (@CARD a0 x0) (@CARD a0 x1)) \/ ((~ (@FINITE a0 x1)) \/ (~ (@PSUBSET a0 x0 x1)))).
Definition term151 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((~ (x1 = x0)) \/ ((Peano.lt x3 x0) \/ (~ (Peano.lt x2 x1))))) -> ~ (x2 = x3).
Definition term57 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ ((fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> (@PSUBSET a0 x0 y0) = (Peano.lt (@CARD a0 x0) (@CARD a0 y0))) x1).
Definition term169 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@CARD a0 x1) = (@CARD a0 x1)) /\ ((~ (Peano.lt (@CARD a0 x1) (@CARD a0 x1))) /\ (Peano.lt (@CARD a0 x0) (@CARD a0 x1))).
Definition term113 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@FINITE a0 x1)) \/ ((Peano.lt (@CARD a0 x0) (@CARD a0 x1)) \/ (~ (@PSUBSET a0 x0 x1))).
Definition term99 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((~ (@SUBSET a0 x0 y0)) \/ ((@CARD a0 x0) = (@CARD a0 y0))) \/ (@PSUBSET a0 x0 y0)) x1.
Definition term80 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@SUBSET a0 x0 x1)) \/ (~ (~ ((@CARD a0 x0) = (@CARD a0 x1)))).
Definition term115 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq Prop ((~ (@PSUBSET a0 x0 x1)) \/ ((~ (@FINITE a0 x1)) \/ (Peano.lt (@CARD a0 x0) (@CARD a0 x1)))).
Definition term97 (x0 : nat) := (fun y0 : nat => ~ (Peano.lt y0 y0)) x0.
Definition term66 (a0 : Type') := exists y0 : a0 -> Prop, exists y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) /\ (((@PSUBSET a0 y0 y1) /\ (~ (Peano.lt (@CARD a0 y0) (@CARD a0 y1)))) \/ ((~ (@PSUBSET a0 y0 y1)) /\ (Peano.lt (@CARD a0 y0) (@CARD a0 y1)))).
Definition term88 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@SUBSET a0 x0 x1) /\ (~ ((@CARD a0 x0) = (@CARD a0 x1))).
Definition term127 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ (@PSUBSET a0 x0 x1)).
Definition term114 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (Peano.lt (@CARD a0 x0) (@CARD a0 x1)) \/ ((~ (@FINITE a0 x1)) \/ (~ (@PSUBSET a0 x0 x1))).
Definition term26 (a0 : Type') (a1 : Type') := (forall y0 : nat, ~ (Peano.lt y0 y0)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@PSUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.lt (@CARD a0 y0) (@CARD a0 y1)) -> (forall y0 : a1 -> Prop, forall y1 : a1 -> Prop, ((@PSUBSET a1 y0 y1) /\ (@FINITE a1 y1)) -> Peano.lt (@CARD a1 y0) (@CARD a1 y1)) -> ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> @PSUBSET a0 y0 y1).
Definition term132 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp ((@PSUBSET a0 x0 x1) /\ (@FINITE a0 x1)).
Definition term164 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x3 = x1) /\ ((~ (Peano.lt x0 x1)) /\ (Peano.lt x2 x3)).
Definition term129 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (@PSUBSET a0 x0 x1).
Definition term21 (a0 : Type') (a1 : Type') := (forall y0 : a1 -> Prop, forall y1 : a1 -> Prop, ((@PSUBSET a1 y0 y1) /\ (@FINITE a1 y1)) -> Peano.lt (@CARD a1 y0) (@CARD a1 y1)) -> ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> @PSUBSET a0 y0 y1).
Definition term130 (a0 : Type') (x0 : a0 -> Prop) := ~ (~ (@FINITE a0 x0)).
Definition term140 (x0 : Prop) (x1 : Prop) := (~ x0) \/ x1.
Definition term159 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (Peano.lt x0 x1)) /\ (~ (~ (Peano.lt x2 x3))).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => forall y1 : Prop, (x0 \/ (y0 \/ y1)) = ((x0 \/ y0) \/ y1)) x1.
Definition term87 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((~ (@SUBSET a0 x0 x1)) \/ ((@CARD a0 x0) = (@CARD a0 x1))) \/ (@PSUBSET a0 x0 x1).
Definition term172 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@CARD a0 x0) = (@CARD a0 x1)) \/ ((~ (@SUBSET a0 x0 x1)) \/ (@PSUBSET a0 x0 x1)).
Definition term134 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (Peano.lt (@CARD a0 x0) (@CARD a0 x1)) -> False.
Definition term179 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@CARD a0 x0) = (@CARD a0 x1)) \/ (~ (@SUBSET a0 x0 x1)).
Definition term118 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or (Peano.lt (@CARD a0 x0) (@CARD a0 x1)).
Definition term65 (a0 : Type') := fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) /\ (((@PSUBSET a0 y0 y1) /\ (~ (Peano.lt (@CARD a0 y0) (@CARD a0 y1)))) \/ ((~ (@PSUBSET a0 y0 y1)) /\ (Peano.lt (@CARD a0 y0) (@CARD a0 y1)))).
Definition term173 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@SUBSET a0 x0 x1)) \/ (@PSUBSET a0 x0 x1).
Definition term4 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (fun y0 : Prop => (x0 \/ (x1 \/ y0)) = ((x0 \/ x1) \/ y0)) x2.
Definition term75 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((~ (@PSUBSET a0 x0 y0)) \/ (~ (@FINITE a0 y0))) \/ (Peano.lt (@CARD a0 x0) (@CARD a0 y0)).
Definition term30 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((@SUBSET a0 x0 y0) /\ (~ ((@CARD a0 x0) = (@CARD a0 y0)))) -> @PSUBSET a0 x0 y0.
Definition term28 (a0 : Type') (a1 : Type') := (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> (@PSUBSET a0 y0 y1) = (Peano.lt (@CARD a0 y0) (@CARD a0 y1)))) -> (forall y0 : nat, ~ (Peano.lt y0 y0)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@PSUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.lt (@CARD a0 y0) (@CARD a0 y1)) -> (forall y0 : a1 -> Prop, forall y1 : a1 -> Prop, ((@PSUBSET a1 y0 y1) /\ (@FINITE a1 y1)) -> Peano.lt (@CARD a1 y0) (@CARD a1 y1)) -> ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> @PSUBSET a0 y0 y1).
Definition term25 (a0 : Type') (a1 : Type') := (forall y0 : nat, ~ (Peano.lt y0 y0)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@PSUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.lt (@CARD a0 y0) (@CARD a0 y1)) -> (forall y0 : a1 -> Prop, forall y1 : a1 -> Prop, ((@PSUBSET a1 y0 y1) /\ (@FINITE a1 y1)) -> Peano.lt (@CARD a1 y0) (@CARD a1 y1)) -> (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> @PSUBSET a0 y0 y1) -> False.
Definition term155 (x0 : nat) (x1 : nat) := ~ (~ (x0 = x1)).
Definition term181 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@PSUBSET a0 x0 x1) \/ ((~ (@SUBSET a0 x0 x1)) \/ ((@CARD a0 x0) = (@CARD a0 x1))).
Definition term186 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ (@SUBSET a0 x0 x1)).
Definition term143 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x2 = x0)) \/ ((~ (x3 = x1)) \/ ((Peano.lt x0 x1) \/ (~ (Peano.lt x2 x3)))).
Definition term74 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((~ (@PSUBSET a0 x0 y0)) \/ (~ (@FINITE a0 y0))) \/ (Peano.lt (@CARD a0 x0) (@CARD a0 y0)).
Definition term96 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((~ (@PSUBSET a0 x0 y0)) \/ (~ (@FINITE a0 y0))) \/ (Peano.lt (@CARD a0 x0) (@CARD a0 y0))) x1.
Definition term46 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := Peano.lt (@CARD a0 x0) (@CARD a0 x1).
Definition term31 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@SUBSET a0 x0 y0) /\ (~ ((@CARD a0 x0) = (@CARD a0 y0)))) -> @PSUBSET a0 x0 y0.
Definition term149 (a0 : Type') (x0 : a0 -> Prop) := Peano.lt (@CARD a0 x0) (@CARD a0 x0).
Definition term27 (a0 : Type') := imp (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> (@PSUBSET a0 y0 y1) = (Peano.lt (@CARD a0 y0) (@CARD a0 y1)))).
Definition term91 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((~ (@SUBSET a0 y0 y1)) \/ ((@CARD a0 y0) = (@CARD a0 y1))) \/ (@PSUBSET a0 y0 y1).
Definition term32 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (~ ((@CARD a0 y0) = (@CARD a0 y1)))) -> @PSUBSET a0 y0 y1.
Definition term150 (x0 : Prop) := x0 -> ~ x0.
Definition term70 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := or ((~ (@PSUBSET a0 x0 x1)) \/ (~ (@FINITE a0 x1))).
Definition term100 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (@PSUBSET a0 x0 x1)) \/ ((~ (@FINITE a0 x1)) \/ (Peano.lt (@CARD a0 x0) (@CARD a0 x1))).
Definition term176 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@CARD a0 x0) = (@CARD a0 x1)) \/ ((@PSUBSET a0 x0 x1) \/ (~ (@SUBSET a0 x0 x1))).
