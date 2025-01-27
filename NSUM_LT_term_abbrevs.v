Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term68 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := or ((x0 x1) /\ (~ ((x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2)))))).
Definition term100 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> nat, forall y2 : a0 -> Prop, (@FINITE a0 y2) -> (@nsum a0 (@INSERT a0 y0 y2) y1) = (@COND nat (@IN a0 y0 y2) (@nsum a0 y2 y1) (Nat.add (y1 y0) (@nsum a0 y2 y1))).
Definition term80 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => ~ (x0 y0)) x1.
Definition term120 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) := Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (x0 x1) /\ ((~ (x1 = x2)) /\ ((~ (x0 x1)) \/ (x1 = x2))).
Definition term86 := (~ False) -> False.
Definition term157 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) (x3 : a0) := (fun y0 : a0 => (@IN a0 y0 x0) -> Peano.le (x1 y0) (x2 y0)) x3.
Definition term96 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (@FINITE a0 (@DELETE a0 y0 y1)) = (@FINITE a0 y0)) x0.
Definition term161 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0 -> nat) := ((Peano.lt (x0 x2) (x3 x2)) /\ (Peano.le (@nsum a0 (@DELETE a0 x1 x2) x0) (@nsum a0 (@DELETE a0 x1 x2) x3))) -> (Peano.lt (Nat.add (x0 x2) (@nsum a0 (@DELETE a0 x1 x2) x0)) (Nat.add (x3 x2) (@nsum a0 (@DELETE a0 x1 x2) x3))) = True.
Definition term94 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, (@IN a0 x1 (@DELETE a0 x0 y0)) = ((@IN a0 x1 x0) /\ (~ (x1 = y0))).
Definition term179 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) (x3 : a0 -> nat) (x4 : a0) := (@IN a0 x4 (@DELETE a0 x0 x1)) -> Peano.le (x2 x4) (x3 x4).
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))).
Definition term57 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (~ (x0 x1)).
Definition term64 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ~ ((x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2)))).
Definition term123 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) (x3 : Prop) (x4 : nat) := (fun y0 : nat => forall y1 : nat, ((@IN a0 x1 (@DELETE a0 x0 x1)) = x3) -> (x3 -> (@nsum a0 (@DELETE a0 x0 x1) x2) = y0) -> ((~ x3) -> (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2)) = y1) -> (@COND nat (@IN a0 x1 (@DELETE a0 x0 x1)) (@nsum a0 (@DELETE a0 x0 x1) x2) (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2))) = (@COND nat x3 y0 y1)) x4.
Definition term124 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) (x3 : Prop) (x4 : nat) := forall y0 : nat, ((@IN a0 x1 (@DELETE a0 x0 x1)) = x3) -> (x3 -> (@nsum a0 (@DELETE a0 x0 x1) x2) = x4) -> ((~ x3) -> (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2)) = y0) -> (@COND nat (@IN a0 x1 (@DELETE a0 x0 x1)) (@nsum a0 (@DELETE a0 x0 x1) x2) (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2))) = (@COND nat x3 x4 y0).
Definition term45 (x0 : Prop) := ~ (~ x0).
Definition term147 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.le y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) x0.
Definition term37 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))).
Definition term60 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ~ ((x0 x1) /\ (~ (x1 = x2))).
Definition term155 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x1) /\ (Peano.le x2 x3).
Definition term10 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0 -> nat) := Peano.lt (@nsum a0 (@INSERT a0 x2 (@DELETE a0 x1 x2)) x0) (@nsum a0 (@INSERT a0 x2 (@DELETE a0 x1 x2)) x3).
Definition term74 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => ~ (y0 = x0)) x1.
Definition term93 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => forall y1 : a0, (@IN a0 y0 (@DELETE a0 x0 y1)) = ((@IN a0 y0 x0) /\ (~ (y0 = y1)))) x1.
Definition term89 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (~ ((y1 y0) -> forall y2 : a0, (y1 y2) = ((y2 = y0) \/ ((y1 y2) /\ (~ (y2 = y0)))))) -> False) x0.
Definition term69 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := or ((x0 x1) /\ ((~ (x1 = x2)) /\ ((~ (x0 x1)) \/ (x1 = x2)))).
Definition term23 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (x1 = x0) \/ (@IN a0 x1 x2).
Definition term185 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term173 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) (x3 : a0 -> nat) (x4 : a0) (x5 : Prop) (x6 : Prop) := ((@IN a0 x4 (@DELETE a0 x0 x1)) = x5) -> (x5 -> (Peano.le (x2 x4) (x3 x4)) = x6) -> ((@IN a0 x4 (@DELETE a0 x0 x1)) -> Peano.le (x2 x4) (x3 x4)) = (x5 -> x6).
Definition term107 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) := @nsum a0 (@INSERT a0 x0 x1) x2.
Definition term164 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0 -> nat) := ((@FINITE a0 (@DELETE a0 x1 x2)) /\ (forall y0 : a0, (@IN a0 y0 (@DELETE a0 x1 x2)) -> Peano.le (x0 y0) (x3 y0))) -> (Peano.le (@nsum a0 (@DELETE a0 x1 x2) x0) (@nsum a0 (@DELETE a0 x1 x2) x3)) = True.
Definition term72 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term195 (a0 : Type') := forall y0 : a0 -> nat, forall y1 : a0 -> nat, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ ((forall y3 : a0, (@IN a0 y3 y2) -> Peano.le (y0 y3) (y1 y3)) /\ (exists y3 : a0, (@IN a0 y3 y2) /\ (Peano.lt (y0 y3) (y1 y3))))) -> Peano.lt (@nsum a0 y2 y0) (@nsum a0 y2 y1).
Definition term22 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @IN a0 x0 (@INSERT a0 x1 x2).
Definition term20 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @eq Prop (@IN a0 x0 x1).
Definition term38 (x0 : Prop) := (~ x0) -> False.
Definition term82 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (~ (x0 x1)).
Definition term54 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ ((x0 x1) = ((x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2)))))) -> False.
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) (x2 y0).
Definition term118 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @IN a0 x1 (@DELETE a0 x0 x1).
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ ((x0 x1) -> forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1))))).
Definition term99 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @FINITE a0 (@DELETE a0 x0 x1).
Definition term184 (a0 : Type') := forall y0 : a0, True.
Definition term139 (a0 : Type') (x0 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : a0 -> nat, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (forall y3 : a0, (@IN a0 y3 y2) -> Peano.le (y0 y3) (y1 y3))) -> Peano.le (@nsum a0 y2 y0) (@nsum a0 y2 y1)) x0.
Definition term143 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ (forall y1 : a0, (@IN a0 y1 y0) -> Peano.le (x0 y1) (x1 y1))) -> Peano.le (@nsum a0 y0 x0) (@nsum a0 y0 x1)) x2.
Definition term113 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) := forall y0 : a0, (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = y0) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 y0).
Definition term109 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) := (@FINITE a0 (@DELETE a0 x0 x1)) -> (@nsum a0 (@INSERT a0 x1 (@DELETE a0 x0 x1)) x2) = (@COND nat (@IN a0 x1 (@DELETE a0 x0 x1)) (@nsum a0 (@DELETE a0 x0 x1) x2) (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2))).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) (x3 : a0) := (@IN a0 x3 x0) /\ (Peano.lt (x1 x3) (x2 x3)).
Definition term62 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (x1 = x2)) /\ (~ ((x0 x1) /\ (~ (x1 = x2)))).
Definition term186 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) (x3 : a0 -> nat) := (@FINITE a0 (@DELETE a0 x0 x1)) /\ (forall y0 : a0, (@IN a0 y0 (@DELETE a0 x0 x1)) -> Peano.le (x2 y0) (x3 y0)).
Definition term47 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => (y0 x0) -> forall y1 : a0, (y0 y1) = ((y1 = x0) \/ ((y0 y1) /\ (~ (y1 = x0)))).
Definition term13 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := @eq Prop (Peano.lt (@nsum a0 x1 x0) (@nsum a0 x1 x2)).
Definition term98 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (@FINITE a0 (@DELETE a0 x0 y0)) = (@FINITE a0 x0)) x1.
Definition term119 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) := @nsum a0 (@DELETE a0 x0 x1) x2.
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term84 (x0 : Prop) := (~ x0) -> x0.
Definition term175 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) (x2 : a0 -> Prop) (x3 : a0) (x4 : a0) (x5 : Prop) := (((@IN a0 x3 x2) /\ (~ (x3 = x4))) -> (Peano.le (x0 x3) (x1 x3)) = x5) -> ((@IN a0 x3 (@DELETE a0 x2 x4)) -> Peano.le (x0 x3) (x1 x3)) = (((@IN a0 x3 x2) /\ (~ (x3 = x4))) -> x5).
Definition term26 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := @IN a0 x0 (@DELETE a0 x1 x2).
Definition term158 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) (x3 : a0) := (@IN a0 x3 x0) -> Peano.le (x1 x3) (x2 x3).
Definition term71 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ((x0 x1) /\ ((~ (x1 = x2)) /\ ((~ (x0 x1)) \/ (x1 = x2)))) \/ ((~ (x0 x1)) /\ ((x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2))))).
Definition term131 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) (x3 : nat) := (False -> (@nsum a0 (@DELETE a0 x0 x1) x2) = (@nsum a0 (@DELETE a0 x0 x1) x2)) -> ((~ False) -> (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2)) = x3) -> (@COND nat (@IN a0 x1 (@DELETE a0 x0 x1)) (@nsum a0 (@DELETE a0 x0 x1) x2) (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2))) = (@COND nat False (@nsum a0 (@DELETE a0 x0 x1) x2) x3).
Definition term25 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := (x0 = x2) \/ (@IN a0 x0 (@DELETE a0 x1 x2)).
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop (x0 x1).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := exists y0 : a0, (@IN a0 y0 x0) /\ (Peano.lt (x1 y0) (x2 y0)).
Definition term111 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) := @COND nat (@IN a0 x1 (@DELETE a0 x0 x1)) (@nsum a0 (@DELETE a0 x0 x1) x2) (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2)).
Definition term79 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => ~ (x0 y0).
Definition term44 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (~ ((x0 x1) -> forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))))).
Definition term180 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ((@IN a0 x1 x0) /\ (~ (x1 = x2))) -> True.
Definition term146 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := Peano.le (@nsum a0 x1 x0) (@nsum a0 x1 x2).
Definition term141 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (forall y2 : a0, (@IN a0 y2 y1) -> Peano.le (x0 y2) (y0 y2))) -> Peano.le (@nsum a0 y1 x0) (@nsum a0 y1 y0)) x1.
Definition term103 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@nsum a0 (@INSERT a0 x0 y1) y0) = (@COND nat (@IN a0 x0 y1) (@nsum a0 y1 y0) (Nat.add (y0 x0) (@nsum a0 y1 y0)))) x1.
Definition term106 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) := (@FINITE a0 x1) -> (@nsum a0 (@INSERT a0 x0 x1) x2) = (@COND nat (@IN a0 x0 x1) (@nsum a0 x1 x2) (Nat.add (x2 x0) (@nsum a0 x1 x2))).
Definition term188 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0 -> nat) := (Peano.lt (x0 x2) (x3 x2)) /\ (Peano.le (@nsum a0 (@DELETE a0 x1 x2) x0) (@nsum a0 (@DELETE a0 x1 x2) x3)).
Definition term50 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, (~ ((y1 y0) -> forall y2 : a0, (y1 y2) = ((y2 = y0) \/ ((y1 y2) /\ (~ (y2 = y0)))))) -> False.
Definition term190 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := (exists y0 : a0, (@IN a0 y0 x1) /\ (Peano.lt (x0 y0) (x2 y0))) -> Peano.lt (@nsum a0 x1 x0) (@nsum a0 x1 x2).
Definition term144 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := ((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x0 y0) (x2 y0))) -> Peano.le (@nsum a0 x1 x0) (@nsum a0 x1 x2).
Definition term5 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) (x2 : a0) := Peano.lt (x0 x2) (x1 x2).
Definition term172 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) (x3 : a0 -> nat) (x4 : a0) (x5 : Prop) (x6 : Prop) := (fun y0 : Prop => ((@IN a0 x4 (@DELETE a0 x0 x1)) = x5) -> (x5 -> (Peano.le (x2 x4) (x3 x4)) = y0) -> ((@IN a0 x4 (@DELETE a0 x0 x1)) -> Peano.le (x2 x4) (x3 x4)) = (x5 -> y0)) x6.
Definition term166 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term9 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) (x2 : a0 -> Prop) (x3 : a0) := (fun y0 : a0 -> Prop => Peano.lt (@nsum a0 y0 x0) (@nsum a0 y0 x1)) (@INSERT a0 x3 (@DELETE a0 x2 x3)).
Definition term76 (a0 : Type') (x0 : a0) := ~ (x0 = x0).
Definition term28 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@IN a0 x0 x1).
Definition term12 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := Peano.lt (@nsum a0 x1 x0) (@nsum a0 x1 x2).
Definition term8 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => Peano.lt (@nsum a0 y0 x0) (@nsum a0 y0 x1)) x2.
Definition term136 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) := Peano.lt (@nsum a0 (@INSERT a0 x1 (@DELETE a0 x0 x1)) x2).
Definition term41 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ((~ ((x0 x1) -> forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))))) -> False) -> (~ ((x0 x1) -> forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))))) -> False.
Definition term170 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) (x3 : a0 -> nat) (x4 : a0) (x5 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@IN a0 x4 (@DELETE a0 x0 x1)) = y0) -> (y0 -> (Peano.le (x2 x4) (x3 x4)) = y1) -> ((@IN a0 x4 (@DELETE a0 x0 x1)) -> Peano.le (x2 x4) (x3 x4)) = (y0 -> y1)) x5.
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (@IN a0 x1 x0) -> forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 (@INSERT a0 x1 (@DELETE a0 x0 x1))).
Definition term104 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@nsum a0 (@INSERT a0 x0 y0) x1) = (@COND nat (@IN a0 x0 y0) (@nsum a0 y0 x1) (Nat.add (x1 x0) (@nsum a0 y0 x1))).
Definition term177 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) (x3 : a0 -> nat) (x4 : a0) := ((@IN a0 x4 x0) /\ (~ (x4 = x1))) -> (Peano.le (x2 x4) (x3 x4)) = True.
Definition term178 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) (x2 : a0 -> Prop) (x3 : a0) (x4 : a0) := (((@IN a0 x3 x2) /\ (~ (x3 = x4))) -> (Peano.le (x0 x3) (x1 x3)) = True) -> ((@IN a0 x3 (@DELETE a0 x2 x4)) -> Peano.le (x0 x3) (x1 x3)) = (((@IN a0 x3 x2) /\ (~ (x3 = x4))) -> True).
Definition term150 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.le x1 y1)) -> Peano.lt (Nat.add x0 x1) (Nat.add y0 y1).
Definition term148 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt x0 y1) /\ (Peano.le y0 y2)) -> Peano.lt (Nat.add x0 y0) (Nat.add y1 y2).
Definition term122 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) (x3 : Prop) := forall y0 : nat, forall y1 : nat, ((@IN a0 x1 (@DELETE a0 x0 x1)) = x3) -> (x3 -> (@nsum a0 (@DELETE a0 x0 x1) x2) = y0) -> ((~ x3) -> (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2)) = y1) -> (@COND nat (@IN a0 x1 (@DELETE a0 x0 x1)) (@nsum a0 (@DELETE a0 x0 x1) x2) (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2))) = (@COND nat x3 y0 y1).
Definition term182 (a0 : Type') := fun y0 : a0 => True.
Definition term61 (a0 : Type') (x0 : a0) (x1 : a0) := and (~ (x0 = x1)).
Definition term151 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.le x1 y1)) -> Peano.lt (Nat.add x0 x1) (Nat.add y0 y1)) x2.
Definition term29 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (x0 x1).
Definition term149 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt x0 y1) /\ (Peano.le y0 y2)) -> Peano.lt (Nat.add x0 y0) (Nat.add y1 y2)) x1.
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (@IN a0 x1 x0) /\ (~ (x1 = x2)).
Definition term81 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @eq Prop ((fun y0 : a0 => ~ (x0 y0)) x1).
Definition term77 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop ((fun y0 : a0 => ~ (y0 = x0)) x1).
Definition term126 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) (x3 : Prop) (x4 : nat) (x5 : nat) := ((@IN a0 x1 (@DELETE a0 x0 x1)) = x3) -> (x3 -> (@nsum a0 (@DELETE a0 x0 x1) x2) = x4) -> ((~ x3) -> (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2)) = x5) -> (@COND nat (@IN a0 x1 (@DELETE a0 x0 x1)) (@nsum a0 (@DELETE a0 x0 x1) x2) (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2))) = (@COND nat x3 x4 x5).
Definition term95 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (fun y0 : a0 => (@IN a0 x1 (@DELETE a0 x0 y0)) = ((@IN a0 x1 x0) /\ (~ (x1 = y0)))) x2.
Definition term160 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.lt x0 x2) /\ (Peano.le x1 x3)) -> (Peano.lt (Nat.add x0 x1) (Nat.add x2 x3)) = True.
Definition term153 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((Peano.lt x0 x2) /\ (Peano.le x1 y0)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 y0)) x3.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := (forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) (x2 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (Peano.lt (x1 y0) (x2 y0))).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := @INSERT a0 x1 (@DELETE a0 x0 x1).
Definition term154 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.lt x0 x2) /\ (Peano.le x1 x3)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 x3).
Definition term105 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@nsum a0 (@INSERT a0 x0 y0) x1) = (@COND nat (@IN a0 x0 y0) (@nsum a0 y0 x1) (Nat.add (x1 x0) (@nsum a0 y0 x1)))) x2.
Definition term133 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) := (~ False) -> (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2)) = (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2)).
Definition term137 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) := Peano.lt (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2)).
Definition term51 (a0 : Type') := fun y0 : a0 => forall y1 : a0 -> Prop, (y1 y0) -> forall y2 : a0, (y1 y2) = ((y2 = y0) \/ ((y1 y2) /\ (~ (y2 = y0)))).
Definition term31 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (x0 x1) /\ (~ (x1 = x2)).
Definition term11 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) (x2 : a0 -> Prop) := @eq Prop ((fun y0 : a0 -> Prop => Peano.lt (@nsum a0 y0 x0) (@nsum a0 y0 x1)) x2).
Definition term171 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) (x3 : a0 -> nat) (x4 : a0) (x5 : Prop) := forall y0 : Prop, ((@IN a0 x4 (@DELETE a0 x0 x1)) = x5) -> (x5 -> (Peano.le (x2 x4) (x3 x4)) = y0) -> ((@IN a0 x4 (@DELETE a0 x0 x1)) -> Peano.le (x2 x4) (x3 x4)) = (x5 -> y0).
Definition term167 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term90 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ ((y0 x0) -> forall y1 : a0, (y0 y1) = ((y1 = x0) \/ ((y0 y1) /\ (~ (y1 = x0)))))) -> False) x1.
Definition term159 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) (x2 : a0) := Peano.le (x0 x2) (x1 x2).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => (@IN a0 y0 x0) = (@IN a0 y0 (@INSERT a0 x1 (@DELETE a0 x0 x1))).
Definition term15 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 (@INSERT a0 x1 (@DELETE a0 x0 x1))).
Definition term42 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (((~ ((x0 x1) -> forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))))) -> False) -> (~ ((x0 x1) -> forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))))) -> False) -> (~ ((x0 x1) -> forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))))) -> False.
Definition term48 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (~ ((y0 x0) -> forall y1 : a0, (y0 y1) = ((y1 = x0) \/ ((y0 y1) /\ (~ (y1 = x0)))))) -> False.
Definition term169 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) (x3 : a0 -> nat) (x4 : a0) := forall y0 : Prop, forall y1 : Prop, ((@IN a0 x4 (@DELETE a0 x0 x1)) = y0) -> (y0 -> (Peano.le (x2 x4) (x3 x4)) = y1) -> ((@IN a0 x4 (@DELETE a0 x0 x1)) -> Peano.le (x2 x4) (x3 x4)) = (y0 -> y1).
Definition term168 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term117 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) := forall y0 : Prop, forall y1 : nat, forall y2 : nat, ((@IN a0 x1 (@DELETE a0 x0 x1)) = y0) -> (y0 -> (@nsum a0 (@DELETE a0 x0 x1) x2) = y1) -> ((~ y0) -> (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2)) = y2) -> (@COND nat (@IN a0 x1 (@DELETE a0 x0 x1)) (@nsum a0 (@DELETE a0 x0 x1) x2) (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2))) = (@COND nat y0 y1 y2).
Definition term116 (x0 : Prop) (x1 : nat) (x2 : nat) := forall y0 : Prop, forall y1 : nat, forall y2 : nat, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND nat x0 x1 x2) = (@COND nat y0 y1 y2).
Definition term115 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := forall y0 : Prop, forall y1 : a0, forall y2 : a0, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND a0 x0 x1 x2) = (@COND a0 y0 y1 y2).
Definition term16 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term78 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop (~ (x0 = x1)).
Definition term30 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (x0 = x1).
Definition term32 (a0 : Type') (x0 : a0) (x1 : a0) := or (x0 = x1).
Definition term194 (a0 : Type') (x0 : a0 -> nat) := forall y0 : a0 -> nat, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((forall y2 : a0, (@IN a0 y2 y1) -> Peano.le (x0 y2) (y0 y2)) /\ (exists y2 : a0, (@IN a0 y2 y1) /\ (Peano.lt (x0 y2) (y0 y2))))) -> Peano.lt (@nsum a0 y1 x0) (@nsum a0 y1 y0).
Definition term140 (a0 : Type') (x0 : a0 -> nat) := forall y0 : a0 -> nat, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (forall y2 : a0, (@IN a0 y2 y1) -> Peano.le (x0 y2) (y0 y2))) -> Peano.le (@nsum a0 y1 x0) (@nsum a0 y1 y0).
Definition term102 (a0 : Type') (x0 : a0) := forall y0 : a0 -> nat, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@nsum a0 (@INSERT a0 x0 y1) y0) = (@COND nat (@IN a0 x0 y1) (@nsum a0 y1 y0) (Nat.add (y0 x0) (@nsum a0 y1 y0))).
Definition term66 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (x0 x1) /\ (~ ((x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2))))).
Definition term52 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, (~ ((y1 y0) -> forall y2 : a0, (y1 y2) = ((y2 = y0) \/ ((y1 y2) /\ (~ (y2 = y0)))))) -> False.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := (@FINITE a0 x0) /\ ((forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) (x2 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (Peano.lt (x1 y0) (x2 y0)))).
Definition term156 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.lt (Nat.add x0 x1) (Nat.add x2 x3).
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))).
Definition term189 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := fun y0 : a0 => (@IN a0 y0 x0) /\ (Peano.lt (x1 y0) (x2 y0)).
Definition term108 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) := @COND nat (@IN a0 x0 x1) (@nsum a0 x1 x2) (Nat.add (x2 x0) (@nsum a0 x1 x2)).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp (x0 x1).
Definition term162 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) (x2 : a0) := and (Peano.lt (x0 x2) (x1 x2)).
Definition term135 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) := @COND nat False (@nsum a0 (@DELETE a0 x0 x1) x2) (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2)).
Definition term24 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0) := @IN a0 x0 (@INSERT a0 x2 (@DELETE a0 x1 x2)).
Definition term165 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (@FINITE a0 (@DELETE a0 x0 x1)).
Definition term152 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((Peano.lt x0 x2) /\ (Peano.le x1 y0)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 y0).
Definition term138 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0 -> nat) := Peano.lt (Nat.add (x0 x2) (@nsum a0 (@DELETE a0 x1 x2) x0)) (Nat.add (x3 x2) (@nsum a0 (@DELETE a0 x1 x2) x3)).
Definition term49 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (y0 x0) -> forall y1 : a0, (y0 y1) = ((y1 = x0) \/ ((y0 y1) /\ (~ (y1 = x0)))).
Definition term114 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) := forall y0 : a0, forall y1 : a0, (x0 = x3) -> (x3 -> x1 = y0) -> ((~ x3) -> x2 = y1) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 y0 y1).
Definition term92 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, forall y1 : a0, (@IN a0 y0 (@DELETE a0 x0 y1)) = ((@IN a0 y0 x0) /\ (~ (y0 = y1))).
Definition term65 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (x0 x1)) /\ ((x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2)))).
Definition term87 (a0 : Type') (x0 : a0) := (~ (x0 = x0)) -> x0 = x0.
Definition term130 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) := False -> (@nsum a0 (@DELETE a0 x0 x1) x2) = (@nsum a0 (@DELETE a0 x0 x1) x2).
Definition term145 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := (@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) (x2 y0)).
Definition term134 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) := ((~ False) -> (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2)) = (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2))) -> (@COND nat (@IN a0 x1 (@DELETE a0 x0 x1)) (@nsum a0 (@DELETE a0 x0 x1) x2) (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2))) = (@COND nat False (@nsum a0 (@DELETE a0 x0 x1) x2) (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2))).
Definition term132 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) (x3 : nat) := ((~ False) -> (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2)) = x3) -> (@COND nat (@IN a0 x1 (@DELETE a0 x0 x1)) (@nsum a0 (@DELETE a0 x0 x1) x2) (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2))) = (@COND nat False (@nsum a0 (@DELETE a0 x0 x1) x2) x3).
Definition term176 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) (x3 : a0) := (@IN a0 x3 x0) -> (Peano.le (x1 x3) (x2 x3)) = True.
Definition term73 (a0 : Type') (x0 : a0) := fun y0 : a0 => ~ (y0 = x0).
Definition term85 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term128 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) (x3 : nat) (x4 : nat) := ((@IN a0 x1 (@DELETE a0 x0 x1)) = False) -> (False -> (@nsum a0 (@DELETE a0 x0 x1) x2) = x3) -> ((~ False) -> (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2)) = x4) -> (@COND nat (@IN a0 x1 (@DELETE a0 x0 x1)) (@nsum a0 (@DELETE a0 x0 x1) x2) (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2))) = (@COND nat False x3 x4).
Definition term181 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) (x3 : a0 -> nat) := fun y0 : a0 => (@IN a0 y0 (@DELETE a0 x0 x1)) -> Peano.le (x2 y0) (x3 y0).
Definition term58 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (x0 x1)) \/ (~ (~ (x1 = x2))).
Definition term110 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) := @nsum a0 (@INSERT a0 x1 (@DELETE a0 x0 x1)) x2.
Definition term163 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := ((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x0 y0) (x2 y0))) -> (Peano.le (@nsum a0 x1 x0) (@nsum a0 x1 x2)) = True.
Definition term70 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ((x0 x1) /\ (~ ((x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2)))))) \/ ((~ (x0 x1)) /\ ((x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2))))).
Definition term55 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ~ ((x0 x1) = ((x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2))))).
Definition term183 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) (x3 : a0 -> nat) := forall y0 : a0, (@IN a0 y0 (@DELETE a0 x0 x1)) -> Peano.le (x2 y0) (x3 y0).
Definition term91 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, forall y2 : a0, (@IN a0 y1 (@DELETE a0 y0 y2)) = ((@IN a0 y1 y0) /\ (~ (y1 = y2)))) x0.
Definition term43 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (((~ ((x0 x1) -> forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))))) -> False) -> (~ ((x0 x1) -> forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))))) -> False) -> ((~ ((x0 x1) -> forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))))) -> False) -> (~ ((x0 x1) -> forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))))) -> False.
Definition term46 (a0 : Type') (x0 : a0) := fun y0 : a0 -> Prop => (~ ((y0 x0) -> forall y1 : a0, (y0 y1) = ((y1 = x0) \/ ((y0 y1) /\ (~ (y1 = x0)))))) -> False.
Definition term192 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := ((@FINITE a0 x1) /\ ((forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x0 y0) (x2 y0)) /\ (exists y0 : a0, (@IN a0 y0 x1) /\ (Peano.lt (x0 y0) (x2 y0))))) -> Peano.lt (@nsum a0 x1 x0) (@nsum a0 x1 x2).
Definition term187 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0) (x3 : a0 -> nat) := Peano.le (@nsum a0 (@DELETE a0 x1 x2) x0) (@nsum a0 (@DELETE a0 x1 x2) x3).
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ ((x0 x1) -> forall y0 : a0, (x0 y0) = ((y0 = x1) \/ ((x0 y0) /\ (~ (y0 = x1)))))) -> False.
Definition term193 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ ((forall y1 : a0, (@IN a0 y1 y0) -> Peano.le (x0 y1) (x1 y1)) /\ (exists y1 : a0, (@IN a0 y1 y0) /\ (Peano.lt (x0 y1) (x1 y1))))) -> Peano.lt (@nsum a0 y0 x0) (@nsum a0 y0 x1).
Definition term142 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (forall y1 : a0, (@IN a0 y1 y0) -> Peano.le (x0 y1) (x1 y1))) -> Peano.le (@nsum a0 y0 x0) (@nsum a0 y0 x1).
Definition term97 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@FINITE a0 (@DELETE a0 x0 y0)) = (@FINITE a0 x0).
Definition term59 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (x0 x1)) \/ (x1 = x2).
Definition term127 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (@IN a0 x1 x0) /\ (~ (x1 = x1)).
Definition term121 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) (x3 : Prop) := (fun y0 : Prop => forall y1 : nat, forall y2 : nat, ((@IN a0 x1 (@DELETE a0 x0 x1)) = y0) -> (y0 -> (@nsum a0 (@DELETE a0 x0 x1) x2) = y1) -> ((~ y0) -> (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2)) = y2) -> (@COND nat (@IN a0 x1 (@DELETE a0 x0 x1)) (@nsum a0 (@DELETE a0 x0 x1) x2) (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2))) = (@COND nat y0 y1 y2)) x3.
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (@IN a0 x1 x0) -> x0 = (@INSERT a0 x1 (@DELETE a0 x0 x1)).
Definition term53 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, (y1 y0) -> forall y2 : a0, (y1 y2) = ((y2 = y0) \/ ((y1 y2) /\ (~ (y2 = y0)))).
Definition term191 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := ((forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x0 y0) (x2 y0)) /\ (exists y0 : a0, (@IN a0 y0 x1) /\ (Peano.lt (x0 y0) (x2 y0)))) -> Peano.lt (@nsum a0 x1 x0) (@nsum a0 x1 x2).
Definition term83 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term88 (a0 : Type') (x0 : a0) := (x0 = x0) -> False.
Definition term112 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) (x5 : a0) := (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = x5) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 x5).
Definition term101 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> nat, forall y2 : a0 -> Prop, (@FINITE a0 y2) -> (@nsum a0 (@INSERT a0 y0 y2) y1) = (@COND nat (@IN a0 y0 y2) (@nsum a0 y2 y1) (Nat.add (y1 y0) (@nsum a0 y2 y1)))) x0.
Definition term33 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (x1 = x2) \/ ((x0 x1) /\ (~ (x1 = x2))).
Definition term129 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) (x3 : nat) (x4 : nat) := (False -> (@nsum a0 (@DELETE a0 x0 x1) x2) = x3) -> ((~ False) -> (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2)) = x4) -> (@COND nat (@IN a0 x1 (@DELETE a0 x0 x1)) (@nsum a0 (@DELETE a0 x0 x1) x2) (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2))) = (@COND nat False x3 x4).
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (~ (x1 = x2)) /\ ((~ (x0 x1)) \/ (x1 = x2)).
Definition term125 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> nat) (x3 : Prop) (x4 : nat) (x5 : nat) := (fun y0 : nat => ((@IN a0 x1 (@DELETE a0 x0 x1)) = x3) -> (x3 -> (@nsum a0 (@DELETE a0 x0 x1) x2) = x4) -> ((~ x3) -> (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2)) = y0) -> (@COND nat (@IN a0 x1 (@DELETE a0 x0 x1)) (@nsum a0 (@DELETE a0 x0 x1) x2) (Nat.add (x2 x1) (@nsum a0 (@DELETE a0 x0 x1) x2))) = (@COND nat x3 x4 y0)) x5.
Definition term56 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (~ (x0 = x1)).
Definition term75 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ (y0 = x0)) x0.
Definition term7 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) := fun y0 : a0 -> Prop => Peano.lt (@nsum a0 y0 x0) (@nsum a0 y0 x1).
Definition term174 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) (x2 : a0 -> Prop) (x3 : a0) (x4 : a0) (x5 : Prop) := ((@IN a0 x3 (@DELETE a0 x2 x4)) = ((@IN a0 x3 x2) /\ (~ (x3 = x4)))) -> (((@IN a0 x3 x2) /\ (~ (x3 = x4))) -> (Peano.le (x0 x3) (x1 x3)) = x5) -> ((@IN a0 x3 (@DELETE a0 x2 x4)) -> Peano.le (x0 x3) (x1 x3)) = (((@IN a0 x3 x2) /\ (~ (x3 = x4))) -> x5).
