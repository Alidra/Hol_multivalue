Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term32 (x0 : nat) (x1 : nat) := (@FINITE nat (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x1) y1))) /\ (@SUBSET nat (dotdot x0 x1) (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x1) y1))).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (@FINITE a0 y0) /\ (@SUBSET a0 x0 y0).
Definition term41 (x0 : nat) (x1 : nat) (x2 : nat) := @IN nat x0 (dotdot x1 x2).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x0 y2) y2))) = (x0 y0).
Definition term93 (x0 : nat) (x1 : nat) := exists y0 : nat -> Prop, (@FINITE nat y0) /\ (@SUBSET nat (dotdot x0 x1) y0).
Definition term72 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 (Peano.le x1 x2).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y0 y3) y3))) = (y0 y1)) x0.
Definition term21 (a0 : Type') (x0 : a0 -> Prop) := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) -> @FINITE a0 x0.
Definition term28 (x0 : nat -> Prop) := (exists y0 : nat -> Prop, (@FINITE nat y0) /\ (@SUBSET nat x0 y0)) -> @FINITE nat x0.
Definition term54 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @SETSPEC nat x0 ((Peano.le x1 x2) /\ (Peano.le x2 x3)).
Definition term91 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term84 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x0 x1) /\ (Peano.le x1 x2)) -> (@IN nat x1 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x2) y1))) = True.
Definition term60 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, @SETSPEC nat x0 ((Peano.le x1 y0) /\ (Peano.le y0 x2)) y0.
Definition term80 (x0 : nat) := fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x0) y1.
Definition term79 (x0 : nat) := fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => Peano.le y2 x0) y1) y1.
Definition term62 (x0 : nat) (x1 : nat) := fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((Peano.le x0 y1) /\ (Peano.le y1 x1)) y1.
Definition term61 (x0 : nat) (x1 : nat) := fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => (Peano.le x0 y2) /\ (Peano.le y2 x1)) y1) y1.
Definition term13 (x0 : nat) := (fun y0 : nat => @FINITE nat (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.le y2 y0) y2))) x0.
Definition term69 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le y0 x0) x1.
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x0) /\ (@SUBSET a0 x1 x0)) -> @FINITE a0 x1.
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := (((Peano.le x0 x1) /\ (Peano.le x1 x2)) -> (@IN nat x1 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x2) y1))) = x3) -> ((@IN nat x1 (dotdot x0 x2)) -> @IN nat x1 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x2) y1))) = (((Peano.le x0 x1) /\ (Peano.le x1 x2)) -> x3).
Definition term83 (x0 : nat) (x1 : nat) := @eq Prop (@IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x1) y1))).
Definition term82 (x0 : nat) (x1 : nat) := @eq Prop (@IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => Peano.le y2 x1) y1) y1))).
Definition term65 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (@IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((Peano.le x1 y1) /\ (Peano.le y1 x2)) y1))).
Definition term64 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (@IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => (Peano.le x1 y2) /\ (Peano.le y2 x2)) y1) y1))).
Definition term96 (x0 : nat) := forall y0 : nat, @FINITE nat (dotdot x0 y0).
Definition term43 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@IN nat x1 (dotdot x0 x2)) = y0) -> (y0 -> (@IN nat x1 (@GSPEC nat (fun y2 : nat => exists y3 : nat, @SETSPEC nat y2 (Peano.le y3 x2) y3))) = y1) -> ((@IN nat x1 (dotdot x0 x2)) -> @IN nat x1 (@GSPEC nat (fun y2 : nat => exists y3 : nat, @SETSPEC nat y2 (Peano.le y3 x2) y3))) = (y0 -> y1)) x3.
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1)) x2.
Definition term94 (x0 : nat) (x1 : nat) := fun y0 : nat -> Prop => (@FINITE nat y0) /\ (@SUBSET nat (dotdot x0 x1) y0).
Definition term66 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := ((@IN nat x1 (dotdot x0 x2)) = ((Peano.le x0 x1) /\ (Peano.le x1 x2))) -> (((Peano.le x0 x1) /\ (Peano.le x1 x2)) -> (@IN nat x1 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x2) y1))) = x3) -> ((@IN nat x1 (dotdot x0 x2)) -> @IN nat x1 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x2) y1))) = (((Peano.le x0 x1) /\ (Peano.le x1 x2)) -> x3).
Definition term73 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 ((fun y0 : nat => Peano.le y0 x1) x2) x2.
Definition term37 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term8 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x1 y1) y1)).
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @SETSPEC nat x0 ((fun y0 : nat => (Peano.le x1 y0) /\ (Peano.le y0 x2)) x3).
Definition term71 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 ((fun y0 : nat => Peano.le y0 x1) x2).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> @FINITE a0 x0.
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x1) /\ (@SUBSET a0 x0 x1).
Definition term34 (x0 : nat -> Prop) (x1 : nat -> Prop) := forall y0 : nat, (@IN nat y0 x0) -> @IN nat y0 x1.
Definition term46 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) := ((@IN nat x1 (dotdot x0 x2)) = x3) -> (x3 -> (@IN nat x1 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x2) y1))) = x4) -> ((@IN nat x1 (dotdot x0 x2)) -> @IN nat x1 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x2) y1))) = (x3 -> x4).
Definition term85 (x0 : nat) (x1 : nat) (x2 : nat) := (((Peano.le x0 x1) /\ (Peano.le x1 x2)) -> (@IN nat x1 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x2) y1))) = True) -> ((@IN nat x1 (dotdot x0 x2)) -> @IN nat x1 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x2) y1))) = (((Peano.le x0 x1) /\ (Peano.le x1 x2)) -> True).
Definition term97 := forall y0 : nat, forall y1 : nat, @FINITE nat (dotdot y0 y1).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) := (exists y0 : a0 -> Prop, (@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> @FINITE a0 x0.
Definition term31 (x0 : nat) (x1 : nat) := @SUBSET nat (dotdot x0 x1) (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x1) y1)).
Definition term55 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @SETSPEC nat x0 ((fun y0 : nat => (Peano.le x1 y0) /\ (Peano.le y0 x2)) x3) x3.
Definition term14 (x0 : nat) := @FINITE nat (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x0) y1)).
Definition term90 := forall y0 : nat, True.
Definition term74 (x0 : nat) (x1 : nat) (x2 : nat) := @SETSPEC nat x0 (Peano.le x2 x1) x2.
Definition term16 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) x0.
Definition term9 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@SUBSET a0 y0 y1) = (forall y2 : a0, (@IN a0 y2 y0) -> @IN a0 y2 y1)) x0.
Definition term86 (x0 : nat) (x1 : nat) (x2 : nat) := (@IN nat x1 (dotdot x0 x2)) -> @IN nat x1 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x2) y1)).
Definition term89 := fun y0 : nat => True.
Definition term78 (x0 : nat) (x1 : nat) := exists y0 : nat, @SETSPEC nat x0 (Peano.le y0 x1) y0.
Definition term70 (x0 : nat) := fun y0 : nat => Peano.le y0 x0.
Definition term44 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) := forall y0 : Prop, ((@IN nat x1 (dotdot x0 x2)) = x3) -> (x3 -> (@IN nat x1 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.le y2 x2) y2))) = y0) -> ((@IN nat x1 (dotdot x0 x2)) -> @IN nat x1 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.le y2 x2) y2))) = (x3 -> y0).
Definition term38 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term88 (x0 : nat) (x1 : nat) := fun y0 : nat => (@IN nat y0 (dotdot x0 x1)) -> @IN nat y0 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.le y2 x1) y2)).
Definition term1 (x0 : nat) := forall y0 : nat, (dotdot x0 y0) = (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 ((Peano.le x0 y2) /\ (Peano.le y2 y0)) y2)).
Definition term35 (x0 : nat) (x1 : nat) := forall y0 : nat, (@IN nat y0 (dotdot x0 x1)) -> @IN nat y0 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.le y2 x1) y2)).
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : Prop, forall y1 : Prop, ((@IN nat x1 (dotdot x0 x2)) = y0) -> (y0 -> (@IN nat x1 (@GSPEC nat (fun y2 : nat => exists y3 : nat, @SETSPEC nat y2 (Peano.le y3 x2) y3))) = y1) -> ((@IN nat x1 (dotdot x0 x2)) -> @IN nat x1 (@GSPEC nat (fun y2 : nat => exists y3 : nat, @SETSPEC nat y2 (Peano.le y3 x2) y3))) = (y0 -> y1).
Definition term39 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term15 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (dotdot x0 y0) = (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 ((Peano.le x0 y2) /\ (Peano.le y2 y0)) y2))) x1.
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x0 y2) y2))) = (x0 y0)) x1.
Definition term45 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((@IN nat x1 (dotdot x0 x2)) = x3) -> (x3 -> (@IN nat x1 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.le y2 x2) y2))) = y0) -> ((@IN nat x1 (dotdot x0 x2)) -> @IN nat x1 (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.le y2 x2) y2))) = (x3 -> y0)) x4.
Definition term95 (x0 : nat) (x1 : nat) := @FINITE nat (dotdot x0 x1).
Definition term25 (a0 : Type') := forall y0 : a0 -> Prop, (exists y1 : a0 -> Prop, (@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0.
Definition term58 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => @SETSPEC nat x0 ((Peano.le x1 y0) /\ (Peano.le y0 x2)) y0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (dotdot y0 y1) = (@GSPEC nat (fun y2 : nat => exists y3 : nat, @SETSPEC nat y2 ((Peano.le y0 y3) /\ (Peano.le y3 y1)) y3))) x0.
Definition term76 (x0 : nat) (x1 : nat) := fun y0 : nat => @SETSPEC nat x0 (Peano.le y0 x1) y0.
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term68 (x0 : nat) (x1 : nat) := @IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => Peano.le y2 x1) y1) y1)).
Definition term49 (x0 : nat) (x1 : nat) (x2 : nat) := @IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => (Peano.le x1 y2) /\ (Peano.le y2 x2)) y1) y1)).
Definition term48 (x0 : nat) (x1 : nat -> Prop) := @IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (x1 y1) y1)).
Definition term47 (x0 : nat) (x1 : nat) (x2 : nat) := @IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((Peano.le x1 y1) /\ (Peano.le y1 x2)) y1)).
Definition term42 (x0 : nat) (x1 : nat) := @IN nat x0 (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x1) y1)).
Definition term12 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 x1.
Definition term92 (x0 : Prop) := forall y0 : nat, x0.
Definition term51 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term33 (x0 : nat) (x1 : nat) := True /\ (@SUBSET nat (dotdot x0 x1) (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x1) y1))).
Definition term22 (a0 : Type') (x0 : a0 -> Prop) := exists y0 : a0 -> Prop, (@FINITE a0 y0) /\ (@SUBSET a0 x0 y0).
Definition term56 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @SETSPEC nat x0 ((Peano.le x1 x3) /\ (Peano.le x3 x2)) x3.
Definition term77 (x0 : nat) (x1 : nat) := exists y0 : nat, @SETSPEC nat x0 ((fun y1 : nat => Peano.le y1 x1) y0) y0.
Definition term59 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, @SETSPEC nat x0 ((fun y1 : nat => (Peano.le x1 y1) /\ (Peano.le y1 x2)) y0) y0.
Definition term27 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (exists y1 : a0 -> Prop, (@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) x0.
Definition term87 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x0 x1) /\ (Peano.le x1 x2)) -> True.
Definition term11 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@SUBSET a0 x0 y0) = (forall y1 : a0, (@IN a0 y1 x0) -> @IN a0 y1 y0)) x1.
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> @FINITE a0 x0) x1.
Definition term75 (x0 : nat) (x1 : nat) := fun y0 : nat => @SETSPEC nat x0 ((fun y1 : nat => Peano.le y1 x1) y0) y0.
Definition term57 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => @SETSPEC nat x0 ((fun y1 : nat => (Peano.le x1 y1) /\ (Peano.le y1 x2)) y0) y0.
Definition term30 (x0 : nat) := and (@FINITE nat (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x0) y1))).
Definition term29 (x0 : nat) (x1 : nat) := (exists y0 : nat -> Prop, (@FINITE nat y0) /\ (@SUBSET nat (dotdot x0 x1) y0)) -> @FINITE nat (dotdot x0 x1).
Definition term4 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y0 y3) y3))) = (y0 y1).
Definition term26 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0) -> forall y0 : a0 -> Prop, (exists y1 : a0 -> Prop, (@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0.
Definition term10 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@SUBSET a0 x0 y0) = (forall y1 : a0, (@IN a0 y1 x0) -> @IN a0 y1 y0).
Definition term81 (x0 : nat) := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => Peano.le y2 x0) y1) y1).
Definition term63 (x0 : nat) (x1 : nat) := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((fun y2 : nat => (Peano.le x0 y2) /\ (Peano.le y2 x1)) y1) y1).
Definition term36 (x0 : nat) := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.le y1 x0) y1).
Definition term3 (x0 : nat) (x1 : nat) := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 ((Peano.le x0 y1) /\ (Peano.le y1 x1)) y1).
