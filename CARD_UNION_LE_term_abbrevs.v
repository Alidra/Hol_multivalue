Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term95 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term141 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) -> @FINITE a0 (@DIFF a0 x0 x1).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ (((x1 x2) \/ (x0 x2)) = ((x1 x2) \/ ((x0 x2) /\ (~ (x1 x2))))).
Definition term76 := (~ False) -> False.
Definition term18 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@UNION a0 x1 x2)).
Definition term177 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (forall y2 : a0, ~ ((y0 y2) /\ ((y1 y2) /\ (~ (y0 y2)))))) -> False) x0.
Definition term77 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (forall y2 : a0, ((y0 y2) \/ (y1 y2)) = ((y0 y2) \/ ((y1 y2) /\ (~ (y0 y2)))))) -> False) x0.
Definition term62 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := and (~ ((x0 x2) \/ (x1 x2))).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) \/ (@IN a0 x1 x2).
Definition term54 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (~ (x0 x1)).
Definition term171 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, ~ ((x0 y1) /\ ((y0 y1) /\ (~ (x0 y1)))).
Definition term40 (x0 : Prop) := ~ (~ x0).
Definition term115 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.add y0 y1) (Nat.add y0 y2)) = (Peano.le y1 y2)) x0.
Definition term87 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) x0.
Definition term136 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq nat (@CARD a0 (@UNION a0 x1 (@DIFF a0 x0 x1))).
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (forall y0 : a0, ((x1 y0) \/ (x0 y0)) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0))))).
Definition term119 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.add x0 x1) (Nat.add x0 y0)) = (Peano.le x1 y0)) x2.
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x0 x2) \/ (x1 x2)).
Definition term146 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @INTER a0 x1 (@DIFF a0 x0 x1).
Definition term28 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) /\ (~ (x1 x2)).
Definition term100 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term85 := (forall y0 : nat, forall y1 : nat, (y0 = y1) -> Peano.le y0 y1) -> forall y0 : nat, forall y1 : nat, (y0 = y1) -> Peano.le y0 y1.
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) /\ ((@FINITE a0 x1) /\ ((@INTER a0 x0 x1) = (@EMPTY a0))).
Definition term134 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @CARD a0 (@UNION a0 x1 (@DIFF a0 x0 x1)).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @UNION a0 x1 (@DIFF a0 x0 x1).
Definition term71 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (((x1 x2) \/ (x0 x2)) /\ (~ ((x1 x2) \/ ((x0 x2) /\ (~ (x1 x2)))))) \/ ((~ ((x1 x2) \/ (x0 x2))) /\ ((x1 x2) \/ ((x0 x2) /\ (~ (x1 x2))))).
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term175 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ~ ((y0 y2) /\ ((y1 y2) /\ (~ (y0 y2)))).
Definition term48 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) \/ (y1 y2)) = ((y0 y2) \/ ((y1 y2) /\ (~ (y0 y2)))).
Definition term59 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x1 x2)) /\ (~ ((x0 x2) /\ (~ (x1 x2)))).
Definition term33 (x0 : Prop) := (~ x0) -> False.
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (((x1 x2) \/ (x0 x2)) = ((x1 x2) \/ ((x0 x2) /\ (~ (x1 x2)))))) -> False.
Definition term145 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (@FINITE a0 (@DIFF a0 x0 x1)).
Definition term127 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@SUBSET a0 (@DIFF a0 x1 x0) x1) /\ (@FINITE a0 x1).
Definition term118 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.add x0 x1) (Nat.add x0 y0)) = (Peano.le x1 y0).
Definition term150 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@INTER a0 x1 (@DIFF a0 x0 x1))) = (@IN a0 y0 (@EMPTY a0)).
Definition term94 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> Peano.le x0 x1.
Definition term84 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, (y0 = y1) -> Peano.le y0 y1) -> Peano.le x0 x1.
Definition term98 (x0 : nat) := forall y0 : nat, (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0.
Definition term53 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (~ (x0 x1)).
Definition term120 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.add x1 x0) (Nat.add x1 x2).
Definition term9 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y0) /\ ((@FINITE a0 y1) /\ ((@INTER a0 y0 y1) = (@EMPTY a0)))) -> (@CARD a0 (@UNION a0 y0 y1)) = (Nat.add (@CARD a0 y0) (@CARD a0 y1))) -> forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y0) /\ ((@FINITE a0 y1) /\ ((@INTER a0 y0 y1) = (@EMPTY a0)))) -> (@CARD a0 (@UNION a0 y0 y1)) = (Nat.add (@CARD a0 y0) (@CARD a0 y1)).
Definition term121 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := Peano.le (Nat.add (@CARD a0 x0) (@CARD a0 (@DIFF a0 x1 x0))) (Nat.add (@CARD a0 x0) (@CARD a0 x1)).
Definition term131 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := Peano.le (@CARD a0 (@UNION a0 x1 x0)) (Nat.add (@CARD a0 x1) (@CARD a0 (@DIFF a0 x0 x1))).
Definition term26 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (@IN a0 x0 x1).
Definition term10 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term176 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x1 x2) /\ ((x0 x2) /\ (~ (x1 x2)))) -> False.
Definition term74 (x0 : Prop) := (~ x0) -> x0.
Definition term103 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) /\ (@FINITE a0 x1).
Definition term157 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((x1 x2) /\ ((x0 x2) /\ (~ (x1 x2)))).
Definition term104 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : nat, (Peano.le (@CARD a0 (@UNION a0 x0 x1)) y0) /\ (Peano.le y0 (Nat.add (@CARD a0 x0) (@CARD a0 x1)))) -> Peano.le (@CARD a0 (@UNION a0 x0 x1)) (Nat.add (@CARD a0 x0) (@CARD a0 x1)).
Definition term183 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@FINITE a0 x0) /\ (@FINITE a0 y0)) -> Peano.le (@CARD a0 (@UNION a0 x0 y0)) (Nat.add (@CARD a0 x0) (@CARD a0 y0)).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@FINITE a0 x0) /\ ((@FINITE a0 y0) /\ ((@INTER a0 x0 y0) = (@EMPTY a0)))) -> (@CARD a0 (@UNION a0 x0 y0)) = (Nat.add (@CARD a0 x0) (@CARD a0 y0)).
Definition term91 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0) x2.
Definition term113 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@SUBSET a0 x0 x1) /\ (@FINITE a0 x1).
Definition term139 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@FINITE a0 x0) -> @FINITE a0 (@DIFF a0 x0 y0).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y0) /\ ((@FINITE a0 y1) /\ ((@INTER a0 y0 y1) = (@EMPTY a0)))) -> (@CARD a0 (@UNION a0 y0 y1)) = (Nat.add (@CARD a0 y0) (@CARD a0 y1))) -> (@CARD a0 (@UNION a0 x0 x1)) = (Nat.add (@CARD a0 x0) (@CARD a0 x1)).
Definition term144 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) -> (@FINITE a0 (@DIFF a0 x0 x1)) = True.
Definition term31 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ((x1 y0) \/ (x0 y0)) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))).
Definition term151 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@INTER a0 x1 x2).
Definition term22 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@DIFF a0 x1 x2).
Definition term122 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := Peano.le (@CARD a0 (@DIFF a0 x1 x0)) (@CARD a0 x1).
Definition term117 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.add x0 y0) (Nat.add x0 y1)) = (Peano.le y0 y1)) x1.
Definition term89 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1) x1.
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x0) /\ ((@FINITE a0 x1) /\ ((@INTER a0 x0 x1) = (@EMPTY a0)))) -> (@CARD a0 (@UNION a0 x0 x1)) = (Nat.add (@CARD a0 x0) (@CARD a0 x1)).
Definition term135 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @eq nat (@CARD a0 (@UNION a0 x0 x1)).
Definition term108 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @SUBSET a0 (@DIFF a0 x1 x0) x1.
Definition term149 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x1) /\ ((@FINITE a0 (@DIFF a0 x0 x1)) /\ ((@INTER a0 x1 (@DIFF a0 x0 x1)) = (@EMPTY a0))).
Definition term107 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => @SUBSET a0 (@DIFF a0 x0 y0) x0) x1.
Definition term169 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, ~ ((x0 y1) /\ ((y0 y1) /\ (~ (x0 y1)))).
Definition term13 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@UNION a0 x1 x2).
Definition term111 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@SUBSET a0 x0 y0) /\ (@FINITE a0 y0)) -> Peano.le (@CARD a0 x0) (@CARD a0 y0)) x1.
Definition term143 (a0 : Type') (x0 : a0 -> Prop) := and (@FINITE a0 x0).
Definition term126 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (@SUBSET a0 (@DIFF a0 x1 x0) x1).
Definition term112 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@SUBSET a0 x0 x1) /\ (@FINITE a0 x1)) -> Peano.le (@CARD a0 x0) (@CARD a0 x1).
Definition term110 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@SUBSET a0 x0 y0) /\ (@FINITE a0 y0)) -> Peano.le (@CARD a0 x0) (@CARD a0 y0).
Definition term30 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@UNION a0 x1 x0)) = (@IN a0 y0 (@UNION a0 x1 (@DIFF a0 x0 x1))).
Definition term24 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@IN a0 x0 x1).
Definition term92 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term67 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x1 x2) \/ (x0 x2)) /\ (~ ((x1 x2) \/ ((x0 x2) /\ (~ (x1 x2))))).
Definition term181 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := Peano.le (@CARD a0 (@UNION a0 x0 x1)) (Nat.add (@CARD a0 x0) (@CARD a0 x1)).
Definition term123 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @CARD a0 (@DIFF a0 x0 x1).
Definition term68 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((x1 x2) \/ (x0 x2)) /\ ((~ (x1 x2)) /\ ((~ (x0 x2)) \/ (x1 x2))).
Definition term164 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((~ (forall y0 : a0, ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ (forall y0 : a0, ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False.
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((~ (forall y0 : a0, ((x1 y0) \/ (x0 y0)) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ (forall y0 : a0, ((x1 y0) \/ (x0 y0)) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))))) -> False.
Definition term42 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, ((x0 y1) \/ (y0 y1)) = ((x0 y1) \/ ((y0 y1) /\ (~ (x0 y1)))).
Definition term60 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x1 x2)) /\ ((~ (x0 x2)) \/ (x1 x2)).
Definition term32 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, ((x1 y0) \/ (x0 y0)) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))).
Definition term116 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.add x0 y0) (Nat.add x0 y1)) = (Peano.le y0 y1).
Definition term99 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term88 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term86 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term79 := forall y0 : nat, forall y1 : nat, (y0 = y1) -> Peano.le y0 y1.
Definition term174 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (~ (forall y2 : a0, ~ ((y0 y2) /\ ((y1 y2) /\ (~ (y0 y2)))))) -> False.
Definition term47 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (~ (forall y2 : a0, ((y0 y2) \/ (y1 y2)) = ((y0 y2) \/ ((y1 y2) /\ (~ (y0 y2)))))) -> False.
Definition term161 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0)))).
Definition term182 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x0) /\ (@FINITE a0 x1)) -> Peano.le (@CARD a0 (@UNION a0 x0 x1)) (Nat.add (@CARD a0 x0) (@CARD a0 x1)).
Definition term55 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x2)) \/ (~ (~ (x1 x2))).
Definition term156 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@INTER a0 x2 (@DIFF a0 x1 x2))).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (x0 x1).
Definition term57 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x0 x2) /\ (~ (x1 x2))).
Definition term154 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@IN a0 x0 x2) /\ (@IN a0 x0 (@DIFF a0 x1 x2)).
Definition term153 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@INTER a0 x2 (@DIFF a0 x1 x2)).
Definition term106 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, @SUBSET a0 (@DIFF a0 x0 y0) x0.
Definition term82 (x0 : nat) (x1 : nat) := (fun y0 : nat => (x0 = y0) -> Peano.le x0 y0) x1.
Definition term52 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x2)) /\ (~ (x1 x2)).
Definition term12 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@UNION a0 x1 x0)) = (@IN a0 y0 (@UNION a0 x1 (@DIFF a0 x0 x1))).
Definition term163 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (forall y0 : a0, ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0))))).
Definition term138 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@FINITE a0 y0) -> @FINITE a0 (@DIFF a0 y0 y1)) x0.
Definition term109 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@SUBSET a0 y0 y1) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 y0) (@CARD a0 y1)) x0.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@FINITE a0 y0) /\ ((@FINITE a0 y1) /\ ((@INTER a0 y0 y1) = (@EMPTY a0)))) -> (@CARD a0 (@UNION a0 y0 y1)) = (Nat.add (@CARD a0 y0) (@CARD a0 y1))) x0.
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 x0) /\ ((@FINITE a0 y0) /\ ((@INTER a0 x0 y0) = (@EMPTY a0)))) -> (@CARD a0 (@UNION a0 x0 y0)) = (Nat.add (@CARD a0 x0) (@CARD a0 y0))) x1.
Definition term167 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ (forall y0 : a0, ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0)))))).
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ~ (~ (forall y0 : a0, ((x1 y0) \/ (x0 y0)) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))))).
Definition term142 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @FINITE a0 (@DIFF a0 x0 x1).
Definition term130 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (Peano.le (@CARD a0 (@UNION a0 x1 x0)) (Nat.add (@CARD a0 x1) (@CARD a0 (@DIFF a0 x0 x1)))) /\ True.
Definition term162 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (forall y0 : a0, ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False.
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (~ (forall y0 : a0, ((x1 y0) \/ (x0 y0)) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))))) -> False.
Definition term180 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : nat => (Peano.le (@CARD a0 (@UNION a0 x0 x1)) y0) /\ (Peano.le y0 (Nat.add (@CARD a0 x0) (@CARD a0 x1))).
Definition term178 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (forall y1 : a0, ~ ((x0 y1) /\ ((y0 y1) /\ (~ (x0 y1)))))) -> False) x1.
Definition term78 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (forall y1 : a0, ((x0 y1) \/ (y0 y1)) = ((x0 y1) \/ ((y0 y1) /\ (~ (x0 y1)))))) -> False) x1.
Definition term140 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 x0) -> @FINITE a0 (@DIFF a0 x0 y0)) x1.
Definition term165 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ (forall y0 : a0, ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ (forall y0 : a0, ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False.
Definition term37 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, ((x1 y0) \/ (x0 y0)) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ (forall y0 : a0, ((x1 y0) \/ (x0 y0)) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ (forall y0 : a0, ((x1 y0) \/ (x0 y0)) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))))) -> False.
Definition term170 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (~ (forall y1 : a0, ~ ((x0 y1) /\ ((y0 y1) /\ (~ (x0 y1)))))) -> False.
Definition term43 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (~ (forall y1 : a0, ((x0 y1) \/ (y0 y1)) = ((x0 y1) \/ ((y0 y1) /\ (~ (x0 y1)))))) -> False.
Definition term179 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : nat, (Peano.le (@CARD a0 (@UNION a0 x0 x1)) y0) /\ (Peano.le y0 (Nat.add (@CARD a0 x0) (@CARD a0 x1))).
Definition term90 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term29 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x1 x2) \/ ((x0 x2) /\ (~ (x1 x2))).
Definition term184 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y0) /\ (@FINITE a0 y1)) -> Peano.le (@CARD a0 (@UNION a0 y0 y1)) (Nat.add (@CARD a0 y0) (@CARD a0 y1)).
Definition term0 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y0) /\ ((@FINITE a0 y1) /\ ((@INTER a0 y0 y1) = (@EMPTY a0)))) -> (@CARD a0 (@UNION a0 y0 y1)) = (Nat.add (@CARD a0 y0) (@CARD a0 y1)).
Definition term129 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (Peano.le (@CARD a0 (@UNION a0 x0 x1)) (Nat.add (@CARD a0 x0) (@CARD a0 (@DIFF a0 x1 x0)))) /\ (Peano.le (Nat.add (@CARD a0 x0) (@CARD a0 (@DIFF a0 x1 x0))) (Nat.add (@CARD a0 x0) (@CARD a0 x1))).
Definition term65 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ((~ (x1 x2)) /\ (~ (x0 x2))) /\ ((x1 x2) \/ ((x0 x2) /\ (~ (x1 x2)))).
Definition term66 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := and ((x0 x2) \/ (x1 x2)).
Definition term105 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, @SUBSET a0 (@DIFF a0 y0 y1) y0) x0.
Definition term20 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@UNION a0 x2 (@DIFF a0 x1 x2)).
Definition term172 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (forall y2 : a0, ~ ((y0 y2) /\ ((y1 y2) /\ (~ (y0 y2)))))) -> False.
Definition term45 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (~ (forall y2 : a0, ((y0 y2) \/ (y1 y2)) = ((y0 y2) \/ ((y1 y2) /\ (~ (y0 y2)))))) -> False.
Definition term152 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) /\ (@IN a0 x1 x2).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) \/ (x1 x2).
Definition term101 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1) x0.
Definition term80 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (y0 = y1) -> Peano.le y0 y1) x0.
Definition term93 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term148 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := True /\ ((@INTER a0 x1 (@DIFF a0 x0 x1)) = (@EMPTY a0)).
Definition term159 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@INTER a0 x1 (@DIFF a0 x0 x1))) = (@IN a0 y0 (@EMPTY a0)).
Definition term158 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x1 x2) /\ ((x0 x2) /\ (~ (x1 x2)))).
Definition term21 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := (@IN a0 x0 x2) \/ (@IN a0 x0 (@DIFF a0 x1 x2)).
Definition term64 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ ((x1 x2) \/ (x0 x2))) /\ ((x1 x2) \/ ((x0 x2) /\ (~ (x1 x2)))).
Definition term125 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@SUBSET a0 (@DIFF a0 x1 x0) x1) /\ (@FINITE a0 x1)) -> (Peano.le (@CARD a0 (@DIFF a0 x1 x0)) (@CARD a0 x1)) = True.
Definition term124 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@SUBSET a0 x0 x1) /\ (@FINITE a0 x1)) -> (Peano.le (@CARD a0 x0) (@CARD a0 x1)) = True.
Definition term147 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 (@DIFF a0 x0 x1)) /\ ((@INTER a0 x1 (@DIFF a0 x0 x1)) = (@EMPTY a0)).
Definition term56 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x2)) \/ (x1 x2).
Definition term97 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1)) -> Peano.le x0 x1.
Definition term132 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@CARD a0 (@UNION a0 x1 x0)) = (Nat.add (@CARD a0 x1) (@CARD a0 (@DIFF a0 x0 x1)))) -> Peano.le (@CARD a0 (@UNION a0 x1 x0)) (Nat.add (@CARD a0 x1) (@CARD a0 (@DIFF a0 x0 x1))).
Definition term69 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or (((x1 x2) \/ (x0 x2)) /\ (~ ((x1 x2) \/ ((x0 x2) /\ (~ (x1 x2)))))).
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := and ((~ (x0 x2)) /\ (~ (x1 x2))).
Definition term75 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) /\ (~ (@IN a0 x1 x2)).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := @eq Prop ((x0 x2) \/ (x1 x2)).
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x1 x2) \/ ((x0 x2) /\ (~ (x1 x2)))).
Definition term133 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := Nat.add (@CARD a0 x1) (@CARD a0 (@DIFF a0 x0 x1)).
Definition term83 (x0 : nat) (x1 : nat) := (x0 = x1) -> Peano.le x0 x1.
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @CARD a0 (@UNION a0 x0 x1).
Definition term96 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term137 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x1) /\ ((@FINITE a0 (@DIFF a0 x0 x1)) /\ ((@INTER a0 x1 (@DIFF a0 x0 x1)) = (@EMPTY a0)))) -> (@CARD a0 (@UNION a0 x1 (@DIFF a0 x0 x1))) = (Nat.add (@CARD a0 x1) (@CARD a0 (@DIFF a0 x0 x1))).
Definition term173 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, ~ ((y0 y2) /\ ((y1 y2) /\ (~ (y0 y2)))).
Definition term46 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, ((y0 y2) \/ (y1 y2)) = ((y0 y2) \/ ((y1 y2) /\ (~ (y0 y2)))).
Definition term166 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ (forall y0 : a0, ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> ((~ (forall y0 : a0, ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ (forall y0 : a0, ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0)))))) -> False.
Definition term38 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (((~ (forall y0 : a0, ((x1 y0) \/ (x0 y0)) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ (forall y0 : a0, ((x1 y0) \/ (x0 y0)) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> ((~ (forall y0 : a0, ((x1 y0) \/ (x0 y0)) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))))) -> False) -> (~ (forall y0 : a0, ((x1 y0) \/ (x0 y0)) = ((x1 y0) \/ ((x0 y0) /\ (~ (x1 y0)))))) -> False.
Definition term168 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (~ (forall y1 : a0, ~ ((x0 y1) /\ ((y0 y1) /\ (~ (x0 y1)))))) -> False.
Definition term41 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (~ (forall y1 : a0, ((x0 y1) \/ (y0 y1)) = ((x0 y1) \/ ((y0 y1) /\ (~ (x0 y1)))))) -> False.
Definition term15 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := or (@IN a0 x0 x1).
Definition term81 (x0 : nat) := forall y0 : nat, (x0 = y0) -> Peano.le x0 y0.
Definition term155 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x1 x2) /\ ((x0 x2) /\ (~ (x1 x2))).
Definition term70 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or (((x1 x2) \/ (x0 x2)) /\ ((~ (x1 x2)) /\ ((~ (x0 x2)) \/ (x1 x2)))).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := Nat.add (@CARD a0 x0) (@CARD a0 x1).
Definition term58 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (~ (x0 x1)).
Definition term73 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term44 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, ((x0 y1) \/ (y0 y1)) = ((x0 y1) \/ ((y0 y1) /\ (~ (x0 y1)))).
Definition term128 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := and (Peano.le (@CARD a0 (@UNION a0 x1 x0)) (Nat.add (@CARD a0 x1) (@CARD a0 (@DIFF a0 x0 x1)))).
Definition term114 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := Peano.le (@CARD a0 x0) (@CARD a0 x1).
Definition term102 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0) x1.
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (x0 x1).
Definition term72 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (((x1 x2) \/ (x0 x2)) /\ ((~ (x1 x2)) /\ ((~ (x0 x2)) \/ (x1 x2)))) \/ (((~ (x1 x2)) /\ (~ (x0 x2))) /\ ((x1 x2) \/ ((x0 x2) /\ (~ (x1 x2))))).
Definition term160 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => ~ ((x1 y0) /\ ((x0 y0) /\ (~ (x1 y0)))).
