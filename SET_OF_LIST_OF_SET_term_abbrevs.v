Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term23 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@set_of_list a0 (@list_of_set a0 y0)) = y0) x0.
Definition term32 (a0 : Type') (x0 : a0 -> Prop) := ((~ (@FINITE a0 x0)) \/ ((@set_of_list a0 (@list_of_set a0 x0)) = x0)) /\ ((~ (@FINITE a0 x0)) \/ ((@List.length a0 (@list_of_set a0 x0)) = (@CARD a0 x0))).
Definition term20 (a0 : Type') (x0 : type686 a0) := ~ (all x0).
Definition term53 := (~ False) -> False.
Definition term5 (a0 : Type') := (~ (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@set_of_list a0 (@list_of_set a0 y0)) = y0)) -> (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> ((@set_of_list a0 (@list_of_set a0 y0)) = y0) /\ ((@List.length a0 (@list_of_set a0 y0)) = (@CARD a0 y0))) -> False.
Definition term29 (a0 : Type') (x0 : a0 -> Prop) := ((@set_of_list a0 (@list_of_set a0 x0)) = x0) /\ ((@List.length a0 (@list_of_set a0 x0)) = (@CARD a0 x0)).
Definition term52 (a0 : Type') (x0 : a0 -> Prop) := ((@set_of_list a0 (@list_of_set a0 x0)) = x0) -> False.
Definition term50 (a0 : Type') (x0 : a0 -> Prop) := imp (@FINITE a0 x0).
Definition term47 (x0 : Prop) := ~ (~ x0).
Definition term28 (a0 : Type') (x0 : a0 -> Prop) := (~ (@FINITE a0 x0)) \/ (((@set_of_list a0 (@list_of_set a0 x0)) = x0) /\ ((@List.length a0 (@list_of_set a0 x0)) = (@CARD a0 x0))).
Definition term26 (a0 : Type') := fun y0 : a0 -> Prop => (@FINITE a0 y0) /\ (~ ((@set_of_list a0 (@list_of_set a0 y0)) = y0)).
Definition term0 (x0 : Prop) := (~ x0) -> False.
Definition term46 (a0 : Type') (x0 : a0 -> Prop) := (~ (~ (@FINITE a0 x0))) -> (@set_of_list a0 (@list_of_set a0 x0)) = x0.
Definition term24 (a0 : Type') (x0 : a0 -> Prop) := ~ ((fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@set_of_list a0 (@list_of_set a0 y0)) = y0) x0).
Definition term45 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term44 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (((@set_of_list a0 (@list_of_set a0 x0)) = x0) \/ (~ (@FINITE a0 x0))).
Definition term41 (x0 : Prop) := (~ x0) -> x0.
Definition term49 (a0 : Type') (x0 : a0 -> Prop) := imp (~ (~ (@FINITE a0 x0))).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) := ~ (@FINITE a0 x0).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) /\ (~ ((@set_of_list a0 (@list_of_set a0 x0)) = x0)).
Definition term37 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((~ (@FINITE a0 y0)) \/ ((@set_of_list a0 (@list_of_set a0 y0)) = y0)) /\ ((~ (@FINITE a0 y0)) \/ ((@List.length a0 (@list_of_set a0 y0)) = (@CARD a0 y0)))) x0.
Definition term10 (a0 : Type') := ~ (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> ((@set_of_list a0 (@list_of_set a0 y0)) = y0) /\ ((@List.length a0 (@list_of_set a0 y0)) = (@CARD a0 y0))).
Definition term31 (a0 : Type') := forall y0 : a0 -> Prop, (~ (@FINITE a0 y0)) \/ (((@set_of_list a0 (@list_of_set a0 y0)) = y0) /\ ((@List.length a0 (@list_of_set a0 y0)) = (@CARD a0 y0))).
Definition term22 (a0 : Type') := exists y0 : a0 -> Prop, ~ ((fun y1 : a0 -> Prop => (@FINITE a0 y1) -> (@set_of_list a0 (@list_of_set a0 y1)) = y1) y0).
Definition term7 (a0 : Type') := (((~ (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@set_of_list a0 (@list_of_set a0 y0)) = y0)) -> (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> ((@set_of_list a0 (@list_of_set a0 y0)) = y0) /\ ((@List.length a0 (@list_of_set a0 y0)) = (@CARD a0 y0))) -> False) -> (~ (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@set_of_list a0 (@list_of_set a0 y0)) = y0)) -> (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> ((@set_of_list a0 (@list_of_set a0 y0)) = y0) /\ ((@List.length a0 (@list_of_set a0 y0)) = (@CARD a0 y0))) -> False) -> (~ (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@set_of_list a0 (@list_of_set a0 y0)) = y0)) -> (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> ((@set_of_list a0 (@list_of_set a0 y0)) = y0) /\ ((@List.length a0 (@list_of_set a0 y0)) = (@CARD a0 y0))) -> False.
Definition term35 (a0 : Type') := fun y0 : a0 -> Prop => ((~ (@FINITE a0 y0)) \/ ((@set_of_list a0 (@list_of_set a0 y0)) = y0)) /\ ((~ (@FINITE a0 y0)) \/ ((@List.length a0 (@list_of_set a0 y0)) = (@CARD a0 y0))).
Definition term4 (a0 : Type') := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> ((@set_of_list a0 (@list_of_set a0 y0)) = y0) /\ ((@List.length a0 (@list_of_set a0 y0)) = (@CARD a0 y0)).
Definition term13 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> ((@set_of_list a0 (@list_of_set a0 x0)) = x0) /\ ((@List.length a0 (@list_of_set a0 x0)) = (@CARD a0 x0)).
Definition term25 (a0 : Type') := fun y0 : a0 -> Prop => ~ ((fun y1 : a0 -> Prop => (@FINITE a0 y1) -> (@set_of_list a0 (@list_of_set a0 y1)) = y1) y0).
Definition term14 (a0 : Type') := fun y0 : a0 -> Prop => (@FINITE a0 y0) -> ((@set_of_list a0 (@list_of_set a0 y0)) = y0) /\ ((@List.length a0 (@list_of_set a0 y0)) = (@CARD a0 y0)).
Definition term40 (a0 : Type') (x0 : a0 -> Prop) := (~ (@FINITE a0 x0)) -> @FINITE a0 x0.
Definition term9 (a0 : Type') := (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> ((@set_of_list a0 (@list_of_set a0 y0)) = y0) /\ ((@List.length a0 (@list_of_set a0 y0)) = (@CARD a0 y0))) -> False.
Definition term2 (a0 : Type') := (~ (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@set_of_list a0 (@list_of_set a0 y0)) = y0)) -> False.
Definition term36 (a0 : Type') := forall y0 : a0 -> Prop, ((~ (@FINITE a0 y0)) \/ ((@set_of_list a0 (@list_of_set a0 y0)) = y0)) /\ ((~ (@FINITE a0 y0)) \/ ((@List.length a0 (@list_of_set a0 y0)) = (@CARD a0 y0))).
Definition term43 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop ((~ (@FINITE a0 x0)) \/ ((@set_of_list a0 (@list_of_set a0 x0)) = x0)).
Definition term21 (a0 : Type') (x0 : type686 a0) := exists y0 : a0 -> Prop, ~ (x0 y0).
Definition term42 (a0 : Type') (x0 : a0 -> Prop) := ((@set_of_list a0 (@list_of_set a0 x0)) = x0) \/ (~ (@FINITE a0 x0)).
Definition term15 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> (@set_of_list a0 (@list_of_set a0 x0)) = x0.
Definition term12 (a0 : Type') := (~ (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@set_of_list a0 (@list_of_set a0 y0)) = y0)) -> ~ (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> ((@set_of_list a0 (@list_of_set a0 y0)) = y0) /\ ((@List.length a0 (@list_of_set a0 y0)) = (@CARD a0 y0))).
Definition term3 (a0 : Type') := ~ (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@set_of_list a0 (@list_of_set a0 y0)) = y0).
Definition term48 (a0 : Type') (x0 : a0 -> Prop) := ~ (~ (@FINITE a0 x0)).
Definition term27 (a0 : Type') := exists y0 : a0 -> Prop, (@FINITE a0 y0) /\ (~ ((@set_of_list a0 (@list_of_set a0 y0)) = y0)).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) := @List.length a0 (@list_of_set a0 x0).
Definition term6 (a0 : Type') := ((~ (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@set_of_list a0 (@list_of_set a0 y0)) = y0)) -> (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> ((@set_of_list a0 (@list_of_set a0 y0)) = y0) /\ ((@List.length a0 (@list_of_set a0 y0)) = (@CARD a0 y0))) -> False) -> (~ (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@set_of_list a0 (@list_of_set a0 y0)) = y0)) -> (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> ((@set_of_list a0 (@list_of_set a0 y0)) = y0) /\ ((@List.length a0 (@list_of_set a0 y0)) = (@CARD a0 y0))) -> False.
Definition term16 (a0 : Type') := fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@set_of_list a0 (@list_of_set a0 y0)) = y0.
Definition term8 (a0 : Type') := (((~ (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@set_of_list a0 (@list_of_set a0 y0)) = y0)) -> (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> ((@set_of_list a0 (@list_of_set a0 y0)) = y0) /\ ((@List.length a0 (@list_of_set a0 y0)) = (@CARD a0 y0))) -> False) -> (~ (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@set_of_list a0 (@list_of_set a0 y0)) = y0)) -> (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> ((@set_of_list a0 (@list_of_set a0 y0)) = y0) /\ ((@List.length a0 (@list_of_set a0 y0)) = (@CARD a0 y0))) -> False) -> ((~ (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@set_of_list a0 (@list_of_set a0 y0)) = y0)) -> (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> ((@set_of_list a0 (@list_of_set a0 y0)) = y0) /\ ((@List.length a0 (@list_of_set a0 y0)) = (@CARD a0 y0))) -> False) -> (~ (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@set_of_list a0 (@list_of_set a0 y0)) = y0)) -> (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> ((@set_of_list a0 (@list_of_set a0 y0)) = y0) /\ ((@List.length a0 (@list_of_set a0 y0)) = (@CARD a0 y0))) -> False.
Definition term51 (a0 : Type') (x0 : a0 -> Prop) := (~ ((@set_of_list a0 (@list_of_set a0 x0)) = x0)) -> (@set_of_list a0 (@list_of_set a0 x0)) = x0.
Definition term38 (a0 : Type') (x0 : a0 -> Prop) := ~ ((@set_of_list a0 (@list_of_set a0 x0)) = x0).
Definition term30 (a0 : Type') := fun y0 : a0 -> Prop => (~ (@FINITE a0 y0)) \/ (((@set_of_list a0 (@list_of_set a0 y0)) = y0) /\ ((@List.length a0 (@list_of_set a0 y0)) = (@CARD a0 y0))).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) := ~ ((@FINITE a0 x0) -> (@set_of_list a0 (@list_of_set a0 x0)) = x0).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) := @set_of_list a0 (@list_of_set a0 x0).
Definition term39 (a0 : Type') (x0 : a0 -> Prop) := (~ (@FINITE a0 x0)) \/ ((@set_of_list a0 (@list_of_set a0 x0)) = x0).
Definition term1 (a0 : Type') := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@set_of_list a0 (@list_of_set a0 y0)) = y0.
Definition term11 (a0 : Type') := imp (~ (forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@set_of_list a0 (@list_of_set a0 y0)) = y0)).
