Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term45 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @COND nat (@IN a0 x0 x1) (@ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) x1 (NUMERAL 0)) ((fun y0 : a0 => fun y1 : nat => S y1) x0 (@ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) x1 (NUMERAL 0))).
Definition term73 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @COND nat (@IN a0 x0 x1) (@CARD a0 x1).
Definition term69 (a0 : Type') := and ((@CARD a0 (@EMPTY a0)) = (NUMERAL 0)).
Definition term50 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> (@ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) (@INSERT a0 x0 x1) (NUMERAL 0)) = (@COND nat (@IN a0 x0 x1) (@ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) x1 (NUMERAL 0)) ((fun y0 : a0 => fun y1 : nat => S y1) x0 (@ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) x1 (NUMERAL 0)))).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) := imp (@FINITE a0 x0).
Definition term71 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @eq nat (@CARD a0 (@INSERT a0 x0 x1)).
Definition term64 (a0 : Type') := imp ((forall y0 : a0, forall y1 : a0, forall y2 : nat, (~ (y0 = y1)) -> ((fun y3 : a0 => fun y4 : nat => S y4) y0 ((fun y3 : a0 => fun y4 : nat => S y4) y1 y2)) = ((fun y3 : a0 => fun y4 : nat => S y4) y1 ((fun y3 : a0 => fun y4 : nat => S y4) y0 y2))) -> ((@ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) (@EMPTY a0) (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) (@INSERT a0 y0 y1) (NUMERAL 0)) = (@COND nat (@IN a0 y0 y1) (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) y1 (NUMERAL 0)) ((fun y2 : a0 => fun y3 : nat => S y3) y0 (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) y1 (NUMERAL 0)))))).
Definition term68 (a0 : Type') := @eq nat (@ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) (@EMPTY a0) (NUMERAL 0)).
Definition term28 (a0 : Type') (x0 : a0) (x1 : a0) := fun y0 : nat => (~ (x1 = x0)) -> ((fun y1 : a0 => fun y2 : nat => S y2) x1 ((fun y1 : a0 => fun y2 : nat => S y2) x0 y0)) = ((fun y1 : a0 => fun y2 : nat => S y2) x0 ((fun y1 : a0 => fun y2 : nat => S y2) x1 y0)).
Definition term15 (a0 : Type') (x0 : a0) := @eq (nat -> nat) ((fun y0 : a0 => fun y1 : nat => S y1) x0).
Definition term63 (a0 : Type') := True -> ((@ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) (@EMPTY a0) (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) (@INSERT a0 y0 y1) (NUMERAL 0)) = (@COND nat (@IN a0 y0 y1) (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) y1 (NUMERAL 0)) (S (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) y1 (NUMERAL 0))))).
Definition term66 (a0 : Type') := @ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) (@EMPTY a0) (NUMERAL 0).
Definition term32 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term70 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @CARD a0 (@INSERT a0 x0 x1).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@CARD a0 y0) = (@ITSET nat a0 (fun y1 : a0 => fun y2 : nat => S y2) y0 (NUMERAL 0))) x0.
Definition term51 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> (@ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) (@INSERT a0 x0 x1) (NUMERAL 0)) = (@COND nat (@IN a0 x0 x1) (@ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) x1 (NUMERAL 0)) (S (@ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) x1 (NUMERAL 0)))).
Definition term24 (a0 : Type') (x0 : a0) (x1 : a0) := imp (~ (x0 = x1)).
Definition term53 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@ITSET nat a0 (fun y1 : a0 => fun y2 : nat => S y2) (@INSERT a0 x0 y0) (NUMERAL 0)) = (@COND nat (@IN a0 x0 y0) (@ITSET nat a0 (fun y1 : a0 => fun y2 : nat => S y2) y0 (NUMERAL 0)) (S (@ITSET nat a0 (fun y1 : a0 => fun y2 : nat => S y2) y0 (NUMERAL 0)))).
Definition term19 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : nat) := (fun y0 : a0 => fun y1 : nat => S y1) x0 ((fun y0 : a0 => fun y1 : nat => S y1) x1 x2).
Definition term37 (a0 : Type') := forall y0 : a0, True.
Definition term76 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> (@CARD a0 (@INSERT a0 x0 x1)) = (@COND nat (@IN a0 x0 x1) (@CARD a0 x1) (S (@CARD a0 x1))).
Definition term65 (a0 : Type') := imp (((@ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) (@EMPTY a0) (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) (@INSERT a0 y0 y1) (NUMERAL 0)) = (@COND nat (@IN a0 y0 y1) (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) y1 (NUMERAL 0)) (S (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) y1 (NUMERAL 0)))))).
Definition term79 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@CARD a0 (@INSERT a0 y0 y1)) = (@COND nat (@IN a0 y0 y1) (@CARD a0 y1) (S (@CARD a0 y1))).
Definition term57 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) (@INSERT a0 y0 y1) (NUMERAL 0)) = (@COND nat (@IN a0 y0 y1) (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) y1 (NUMERAL 0)) (S (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) y1 (NUMERAL 0)))).
Definition term56 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) (@INSERT a0 y0 y1) (NUMERAL 0)) = (@COND nat (@IN a0 y0 y1) (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) y1 (NUMERAL 0)) ((fun y2 : a0 => fun y3 : nat => S y3) y0 (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) y1 (NUMERAL 0)))).
Definition term21 (x0 : nat) := S (S x0).
Definition term7 (a0 : Type') := (forall y0 : a0, forall y1 : a0, forall y2 : nat, (~ (y0 = y1)) -> ((fun y3 : a0 => fun y4 : nat => S y4) y0 ((fun y3 : a0 => fun y4 : nat => S y4) y1 y2)) = ((fun y3 : a0 => fun y4 : nat => S y4) y1 ((fun y3 : a0 => fun y4 : nat => S y4) y0 y2))) -> ((@ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) (@EMPTY a0) (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) (@INSERT a0 y0 y1) (NUMERAL 0)) = (@COND nat (@IN a0 y0 y1) (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) y1 (NUMERAL 0)) ((fun y2 : a0 => fun y3 : nat => S y3) y0 (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) y1 (NUMERAL 0))))).
Definition term34 (a0 : Type') (x0 : a0) := fun y0 : a0 => forall y1 : nat, (~ (x0 = y0)) -> ((fun y2 : a0 => fun y3 : nat => S y3) x0 ((fun y2 : a0 => fun y3 : nat => S y3) y0 y1)) = ((fun y2 : a0 => fun y3 : nat => S y3) y0 ((fun y2 : a0 => fun y3 : nat => S y3) x0 y1)).
Definition term16 (a0 : Type') (x0 : a0) (x1 : nat) := (fun y0 : a0 => fun y1 : nat => S y1) x0 x1.
Definition term38 (a0 : Type') := fun y0 : a0 => forall y1 : a0, forall y2 : nat, (~ (y0 = y1)) -> ((fun y3 : a0 => fun y4 : nat => S y4) y0 ((fun y3 : a0 => fun y4 : nat => S y4) y1 y2)) = ((fun y3 : a0 => fun y4 : nat => S y4) y1 ((fun y3 : a0 => fun y4 : nat => S y4) y0 y2)).
Definition term14 (a0 : Type') (x0 : a0) := @eq (nat -> nat) ((fun y0 : a0 => (fun y1 : a0 => fun y2 : nat => S y2) y0) x0).
Definition term44 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @COND nat (@IN a0 x0 x1) (@ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) x1 (NUMERAL 0)).
Definition term23 (x0 : nat) := @eq nat (S (S x0)).
Definition term74 (a0 : Type') (x0 : a0 -> Prop) := S (@CARD a0 x0).
Definition term22 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : nat) := @eq nat ((fun y0 : a0 => fun y1 : nat => S y1) x0 ((fun y0 : a0 => fun y1 : nat => S y1) x1 x2)).
Definition term17 (x0 : nat) := (fun y0 : nat => S y0) x0.
Definition term13 (a0 : Type') := fun y0 : a0 => (fun y1 : a0 => fun y2 : nat => S y2) y0.
Definition term30 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : nat, (~ (x1 = x0)) -> ((fun y1 : a0 => fun y2 : nat => S y2) x1 ((fun y1 : a0 => fun y2 : nat => S y2) x0 y0)) = ((fun y1 : a0 => fun y2 : nat => S y2) x0 ((fun y1 : a0 => fun y2 : nat => S y2) x1 y0)).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := @ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) x0 (NUMERAL 0).
Definition term10 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (fun y1 : a0 => fun y2 : nat => S y2) y0) x0.
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term78 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@CARD a0 (@INSERT a0 x0 y0)) = (@COND nat (@IN a0 x0 y0) (@CARD a0 y0) (S (@CARD a0 y0))).
Definition term55 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@ITSET nat a0 (fun y1 : a0 => fun y2 : nat => S y2) (@INSERT a0 x0 y0) (NUMERAL 0)) = (@COND nat (@IN a0 x0 y0) (@ITSET nat a0 (fun y1 : a0 => fun y2 : nat => S y2) y0 (NUMERAL 0)) (S (@ITSET nat a0 (fun y1 : a0 => fun y2 : nat => S y2) y0 (NUMERAL 0)))).
Definition term54 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@ITSET nat a0 (fun y1 : a0 => fun y2 : nat => S y2) (@INSERT a0 x0 y0) (NUMERAL 0)) = (@COND nat (@IN a0 x0 y0) (@ITSET nat a0 (fun y1 : a0 => fun y2 : nat => S y2) y0 (NUMERAL 0)) ((fun y1 : a0 => fun y2 : nat => S y2) x0 (@ITSET nat a0 (fun y1 : a0 => fun y2 : nat => S y2) y0 (NUMERAL 0)))).
Definition term25 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : nat) := (~ (x1 = x0)) -> ((fun y0 : a0 => fun y1 : nat => S y1) x1 ((fun y0 : a0 => fun y1 : nat => S y1) x0 x2)) = ((fun y0 : a0 => fun y1 : nat => S y1) x0 ((fun y0 : a0 => fun y1 : nat => S y1) x1 x2)).
Definition term35 (a0 : Type') := fun y0 : a0 => True.
Definition term52 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@ITSET nat a0 (fun y1 : a0 => fun y2 : nat => S y2) (@INSERT a0 x0 y0) (NUMERAL 0)) = (@COND nat (@IN a0 x0 y0) (@ITSET nat a0 (fun y1 : a0 => fun y2 : nat => S y2) y0 (NUMERAL 0)) ((fun y1 : a0 => fun y2 : nat => S y2) x0 (@ITSET nat a0 (fun y1 : a0 => fun y2 : nat => S y2) y0 (NUMERAL 0)))).
Definition term9 (a0 : Type') (x0 : type1425 a0) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term18 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term40 (a0 : Type') := imp (forall y0 : a0, forall y1 : a0, forall y2 : nat, (~ (y0 = y1)) -> ((fun y3 : a0 => fun y4 : nat => S y4) y0 ((fun y3 : a0 => fun y4 : nat => S y4) y1 y2)) = ((fun y3 : a0 => fun y4 : nat => S y4) y1 ((fun y3 : a0 => fun y4 : nat => S y4) y0 y2))).
Definition term31 := forall y0 : nat, True.
Definition term39 (a0 : Type') := forall y0 : a0, forall y1 : a0, forall y2 : nat, (~ (y0 = y1)) -> ((fun y3 : a0 => fun y4 : nat => S y4) y0 ((fun y3 : a0 => fun y4 : nat => S y4) y1 y2)) = ((fun y3 : a0 => fun y4 : nat => S y4) y1 ((fun y3 : a0 => fun y4 : nat => S y4) y0 y2)).
Definition term75 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @COND nat (@IN a0 x0 x1) (@CARD a0 x1) (S (@CARD a0 x1)).
Definition term62 (a0 : Type') := ((@ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) (@EMPTY a0) (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) (@INSERT a0 y0 y1) (NUMERAL 0)) = (@COND nat (@IN a0 y0 y1) (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) y1 (NUMERAL 0)) (S (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) y1 (NUMERAL 0))))).
Definition term61 (a0 : Type') := ((@ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) (@EMPTY a0) (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) (@INSERT a0 y0 y1) (NUMERAL 0)) = (@COND nat (@IN a0 y0 y1) (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) y1 (NUMERAL 0)) ((fun y2 : a0 => fun y3 : nat => S y3) y0 (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) y1 (NUMERAL 0))))).
Definition term6 (a0 : Type') := (fun y0 : nat => (forall y1 : a0, forall y2 : a0, forall y3 : nat, (~ (y1 = y2)) -> ((fun y4 : a0 => fun y5 : nat => S y5) y1 ((fun y4 : a0 => fun y5 : nat => S y5) y2 y3)) = ((fun y4 : a0 => fun y5 : nat => S y5) y2 ((fun y4 : a0 => fun y5 : nat => S y5) y1 y3))) -> ((@ITSET nat a0 (fun y1 : a0 => fun y2 : nat => S y2) (@EMPTY a0) y0) = y0) /\ (forall y1 : a0, forall y2 : a0 -> Prop, (@FINITE a0 y2) -> (@ITSET nat a0 (fun y3 : a0 => fun y4 : nat => S y4) (@INSERT a0 y1 y2) y0) = (@COND nat (@IN a0 y1 y2) (@ITSET nat a0 (fun y3 : a0 => fun y4 : nat => S y4) y2 y0) ((fun y3 : a0 => fun y4 : nat => S y4) y1 (@ITSET nat a0 (fun y3 : a0 => fun y4 : nat => S y4) y2 y0))))) (NUMERAL 0).
Definition term67 (a0 : Type') := @eq nat (@CARD a0 (@EMPTY a0)).
Definition term29 := fun y0 : nat => True.
Definition term26 (a0 : Type') (x0 : a0) (x1 : a0) := (~ (x0 = x1)) -> True.
Definition term27 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (x0 = x1).
Definition term43 (a0 : Type') (x0 : a0 -> Prop) := S (@ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) x0 (NUMERAL 0)).
Definition term3 (a0 : Type') := (fun y0 : type1425 a0 => forall y1 : nat, (forall y2 : a0, forall y3 : a0, forall y4 : nat, (~ (y2 = y3)) -> (y0 y2 (y0 y3 y4)) = (y0 y3 (y0 y2 y4))) -> ((@ITSET nat a0 y0 (@EMPTY a0) y1) = y1) /\ (forall y2 : a0, forall y3 : a0 -> Prop, (@FINITE a0 y3) -> (@ITSET nat a0 y0 (@INSERT a0 y2 y3) y1) = (@COND nat (@IN a0 y2 y3) (@ITSET nat a0 y0 y3 y1) (y0 y2 (@ITSET nat a0 y0 y3 y1))))) (fun y0 : a0 => fun y1 : nat => S y1).
Definition term4 (a0 : Type') := fun y0 : a0 => fun y1 : nat => S y1.
Definition term2 (a0 : Type') := forall y0 : type1425 a0, forall y1 : nat, (forall y2 : a0, forall y3 : a0, forall y4 : nat, (~ (y2 = y3)) -> (y0 y2 (y0 y3 y4)) = (y0 y3 (y0 y2 y4))) -> ((@ITSET nat a0 y0 (@EMPTY a0) y1) = y1) /\ (forall y2 : a0, forall y3 : a0 -> Prop, (@FINITE a0 y3) -> (@ITSET nat a0 y0 (@INSERT a0 y2 y3) y1) = (@COND nat (@IN a0 y2 y3) (@ITSET nat a0 y0 y3 y1) (y0 y2 (@ITSET nat a0 y0 y3 y1)))).
Definition term20 (x0 : nat) := (fun y0 : nat => S y0) (S x0).
Definition term60 (a0 : Type') := and ((@ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) (@EMPTY a0) (NUMERAL 0)) = (NUMERAL 0)).
Definition term41 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (fun y0 : a0 => fun y1 : nat => S y1) x0 (@ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) x1 (NUMERAL 0)).
Definition term77 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@CARD a0 (@INSERT a0 x0 y0)) = (@COND nat (@IN a0 x0 y0) (@CARD a0 y0) (S (@CARD a0 y0))).
Definition term46 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @COND nat (@IN a0 x0 x1) (@ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) x1 (NUMERAL 0)) (S (@ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) x1 (NUMERAL 0))).
Definition term82 (a0 : Type') := ((forall y0 : a0, forall y1 : a0, forall y2 : nat, (~ (y0 = y1)) -> ((fun y3 : a0 => fun y4 : nat => S y4) y0 ((fun y3 : a0 => fun y4 : nat => S y4) y1 y2)) = ((fun y3 : a0 => fun y4 : nat => S y4) y1 ((fun y3 : a0 => fun y4 : nat => S y4) y0 y2))) -> ((@ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) (@EMPTY a0) (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) (@INSERT a0 y0 y1) (NUMERAL 0)) = (@COND nat (@IN a0 y0 y1) (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) y1 (NUMERAL 0)) ((fun y2 : a0 => fun y3 : nat => S y3) y0 (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) y1 (NUMERAL 0)))))) -> ((@CARD a0 (@EMPTY a0)) = (NUMERAL 0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@CARD a0 (@INSERT a0 y0 y1)) = (@COND nat (@IN a0 y0 y1) (@CARD a0 y1) (S (@CARD a0 y1)))).
Definition term83 (a0 : Type') := (((@ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) (@EMPTY a0) (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) (@INSERT a0 y0 y1) (NUMERAL 0)) = (@COND nat (@IN a0 y0 y1) (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) y1 (NUMERAL 0)) (S (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) y1 (NUMERAL 0)))))) -> ((@ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) (@EMPTY a0) (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) (@INSERT a0 y0 y1) (NUMERAL 0)) = (@COND nat (@IN a0 y0 y1) (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) y1 (NUMERAL 0)) (S (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) y1 (NUMERAL 0))))).
Definition term12 := fun y0 : nat => S y0.
Definition term42 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : nat => S y0) (@ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) x0 (NUMERAL 0)).
Definition term33 (x0 : Prop) := forall y0 : nat, x0.
Definition term5 (a0 : Type') := forall y0 : nat, (forall y1 : a0, forall y2 : a0, forall y3 : nat, (~ (y1 = y2)) -> ((fun y4 : a0 => fun y5 : nat => S y5) y1 ((fun y4 : a0 => fun y5 : nat => S y5) y2 y3)) = ((fun y4 : a0 => fun y5 : nat => S y5) y2 ((fun y4 : a0 => fun y5 : nat => S y5) y1 y3))) -> ((@ITSET nat a0 (fun y1 : a0 => fun y2 : nat => S y2) (@EMPTY a0) y0) = y0) /\ (forall y1 : a0, forall y2 : a0 -> Prop, (@FINITE a0 y2) -> (@ITSET nat a0 (fun y3 : a0 => fun y4 : nat => S y4) (@INSERT a0 y1 y2) y0) = (@COND nat (@IN a0 y1 y2) (@ITSET nat a0 (fun y3 : a0 => fun y4 : nat => S y4) y2 y0) ((fun y3 : a0 => fun y4 : nat => S y4) y1 (@ITSET nat a0 (fun y3 : a0 => fun y4 : nat => S y4) y2 y0)))).
Definition term11 (a0 : Type') (x0 : a0) := (fun y0 : a0 => fun y1 : nat => S y1) x0.
Definition term81 (a0 : Type') := ((@CARD a0 (@EMPTY a0)) = (NUMERAL 0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@CARD a0 (@INSERT a0 y0 y1)) = (@COND nat (@IN a0 y0 y1) (@CARD a0 y1) (S (@CARD a0 y1)))).
Definition term48 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) (@INSERT a0 x0 x1) (NUMERAL 0).
Definition term80 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@CARD a0 (@INSERT a0 y0 y1)) = (@COND nat (@IN a0 y0 y1) (@CARD a0 y1) (S (@CARD a0 y1))).
Definition term59 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) (@INSERT a0 y0 y1) (NUMERAL 0)) = (@COND nat (@IN a0 y0 y1) (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) y1 (NUMERAL 0)) (S (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) y1 (NUMERAL 0)))).
Definition term58 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) (@INSERT a0 y0 y1) (NUMERAL 0)) = (@COND nat (@IN a0 y0 y1) (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) y1 (NUMERAL 0)) ((fun y2 : a0 => fun y3 : nat => S y3) y0 (@ITSET nat a0 (fun y2 : a0 => fun y3 : nat => S y3) y1 (NUMERAL 0)))).
Definition term36 (a0 : Type') (x0 : a0) := forall y0 : a0, forall y1 : nat, (~ (x0 = y0)) -> ((fun y2 : a0 => fun y3 : nat => S y3) x0 ((fun y2 : a0 => fun y3 : nat => S y3) y0 y1)) = ((fun y2 : a0 => fun y3 : nat => S y3) y0 ((fun y2 : a0 => fun y3 : nat => S y3) x0 y1)).
Definition term47 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @eq nat (@ITSET nat a0 (fun y0 : a0 => fun y1 : nat => S y1) (@INSERT a0 x0 x1) (NUMERAL 0)).
Definition term72 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @COND nat (@IN a0 x0 x1).