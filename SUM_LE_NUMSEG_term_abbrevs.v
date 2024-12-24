Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := @IN nat x0 (dotdot x1 x2).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (@IN nat y2 (dotdot y0 y1)) = ((Peano.le y0 y2) /\ (Peano.le y2 y1))) x0.
Definition term24 (x0 : nat -> real) (x1 : nat) (x2 : nat) (x3 : nat -> real) := real_le (@sum nat (dotdot x1 x2) x0) (@sum nat (dotdot x1 x2) x3).
Definition term54 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) (x4 : nat) (x5 : Prop) (x6 : Prop) := ((@IN nat x4 (dotdot x0 x1)) = x5) -> (x5 -> (real_le (x2 x4) (x3 x4)) = x6) -> ((@IN nat x4 (dotdot x0 x1)) -> real_le (x2 x4) (x3 x4)) = (x5 -> x6).
Definition term36 (x0 : nat -> real) (x1 : nat) (x2 : nat) (x3 : nat -> real) := ((@FINITE nat (dotdot x1 x2)) /\ (forall y0 : nat, (@IN nat y0 (dotdot x1 x2)) -> real_le (x0 y0) (x3 y0))) -> (real_le (@sum nat (dotdot x1 x2) x0) (@sum nat (dotdot x1 x2) x3)) = True.
Definition term59 (x0 : nat -> real) (x1 : nat) (x2 : nat) (x3 : nat -> real) := (forall y0 : nat, ((Peano.le x1 y0) /\ (Peano.le y0 x2)) -> real_le (x0 y0) (x3 y0)) -> real_le (@sum nat (dotdot x1 x2) x0) (@sum nat (dotdot x1 x2) x3).
Definition term65 (x0 : nat -> real) := fun y0 : nat -> real => forall y1 : nat, forall y2 : nat, (forall y3 : nat, ((Peano.le y1 y3) /\ (Peano.le y3 y2)) -> real_le (x0 y3) (y0 y3)) -> real_le (@sum nat (dotdot y1 y2) x0) (@sum nat (dotdot y1 y2) y0).
Definition term11 (a0 : Type') (x0 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0 -> real, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (forall y3 : a0, (@IN a0 y3 y2) -> real_le (y0 y3) (y1 y3))) -> real_le (@sum a0 y2 y0) (@sum a0 y2 y1)) x0.
Definition term15 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ (forall y1 : a0, (@IN a0 y1 y0) -> real_le (x0 y1) (x1 y1))) -> real_le (@sum a0 y0 x0) (@sum a0 y0 x1)) x2.
Definition term71 := forall y0 : nat -> real, forall y1 : nat -> real, forall y2 : nat, forall y3 : nat, (forall y4 : nat, ((Peano.le y2 y4) /\ (Peano.le y4 y3)) -> real_le (y0 y4) (y1 y4)) -> real_le (@sum nat (dotdot y2 y3) y0) (@sum nat (dotdot y2 y3) y1).
Definition term67 (x0 : nat -> real) := forall y0 : nat -> real, forall y1 : nat, forall y2 : nat, (forall y3 : nat, ((Peano.le y1 y3) /\ (Peano.le y3 y2)) -> real_le (x0 y3) (y0 y3)) -> real_le (@sum nat (dotdot y1 y2) x0) (@sum nat (dotdot y1 y2) y0).
Definition term28 (x0 : nat -> real) (x1 : nat) (x2 : nat) (x3 : nat -> real) (x4 : Prop) (x5 : Prop) := ((forall y0 : nat, ((Peano.le x1 y0) /\ (Peano.le y0 x2)) -> real_le (x0 y0) (x3 y0)) = x4) -> (x4 -> (real_le (@sum nat (dotdot x1 x2) x0) (@sum nat (dotdot x1 x2) x3)) = x5) -> ((forall y0 : nat, ((Peano.le x1 y0) /\ (Peano.le y0 x2)) -> real_le (x0 y0) (x3 y0)) -> real_le (@sum nat (dotdot x1 x2) x0) (@sum nat (dotdot x1 x2) x3)) = (x4 -> x5).
Definition term44 (x0 : nat -> real) (x1 : nat -> real) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : Prop) := (((Peano.le x2 x3) /\ (Peano.le x3 x4)) -> (real_le (x0 x3) (x1 x3)) = x5) -> ((@IN nat x3 (dotdot x2 x4)) -> real_le (x0 x3) (x1 x3)) = (((Peano.le x2 x3) /\ (Peano.le x3 x4)) -> x5).
Definition term43 (x0 : nat -> real) (x1 : nat -> real) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : Prop) := ((@IN nat x3 (dotdot x2 x4)) = ((Peano.le x2 x3) /\ (Peano.le x3 x4))) -> (((Peano.le x2 x3) /\ (Peano.le x3 x4)) -> (real_le (x0 x3) (x1 x3)) = x5) -> ((@IN nat x3 (dotdot x2 x4)) -> real_le (x0 x3) (x1 x3)) = (((Peano.le x2 x3) /\ (Peano.le x3 x4)) -> x5).
Definition term56 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) := (@FINITE nat (dotdot x0 x1)) /\ (forall y0 : nat, (@IN nat y0 (dotdot x0 x1)) -> real_le (x2 y0) (x3 y0)).
Definition term8 (x0 : nat) := forall y0 : nat, @FINITE nat (dotdot x0 y0).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (@IN nat y1 (dotdot x0 y0)) = ((Peano.le x0 y1) /\ (Peano.le y1 y0))) x1.
Definition term13 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (forall y2 : a0, (@IN a0 y2 y1) -> real_le (x0 y2) (y0 y2))) -> real_le (@sum a0 y1 x0) (@sum a0 y1 y0)) x1.
Definition term9 (x0 : nat) (x1 : nat) := (fun y0 : nat => @FINITE nat (dotdot x0 y0)) x1.
Definition term61 (x0 : nat -> real) (x1 : nat) (x2 : nat -> real) := fun y0 : nat => (forall y1 : nat, ((Peano.le x1 y1) /\ (Peano.le y1 y0)) -> real_le (x0 y1) (x2 y1)) -> real_le (@sum nat (dotdot x1 y0) x0) (@sum nat (dotdot x1 y0) x2).
Definition term45 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) (x4 : nat) := ((Peano.le x0 x4) /\ (Peano.le x4 x1)) -> (real_le (x2 x4) (x3 x4)) = True.
Definition term41 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) (x4 : nat) (x5 : Prop) (x6 : Prop) := (fun y0 : Prop => ((@IN nat x4 (dotdot x0 x1)) = x5) -> (x5 -> (real_le (x2 x4) (x3 x4)) = y0) -> ((@IN nat x4 (dotdot x0 x1)) -> real_le (x2 x4) (x3 x4)) = (x5 -> y0)) x6.
Definition term31 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) (x4 : nat) := (fun y0 : nat => ((Peano.le x0 y0) /\ (Peano.le y0 x1)) -> real_le (x2 y0) (x3 y0)) x4.
Definition term19 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term60 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) := (forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x1)) -> real_le (x2 y0) (x3 y0)) -> True.
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) (x4 : nat) (x5 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@IN nat x4 (dotdot x0 x1)) = y0) -> (y0 -> (real_le (x2 x4) (x3 x4)) = y1) -> ((@IN nat x4 (dotdot x0 x1)) -> real_le (x2 x4) (x3 x4)) = (y0 -> y1)) x5.
Definition term68 := forall y0 : nat -> real, True.
Definition term47 (x0 : nat -> real) (x1 : nat -> real) (x2 : nat) (x3 : nat) (x4 : nat) := (((Peano.le x2 x3) /\ (Peano.le x3 x4)) -> (real_le (x0 x3) (x1 x3)) = True) -> ((@IN nat x3 (dotdot x2 x4)) -> real_le (x0 x3) (x1 x3)) = (((Peano.le x2 x3) /\ (Peano.le x3 x4)) -> True).
Definition term64 (x0 : nat -> real) (x1 : nat -> real) := forall y0 : nat, forall y1 : nat, (forall y2 : nat, ((Peano.le y0 y2) /\ (Peano.le y2 y1)) -> real_le (x0 y2) (x1 y2)) -> real_le (@sum nat (dotdot y0 y1) x0) (@sum nat (dotdot y0 y1) x1).
Definition term1 (x0 : nat) := forall y0 : nat, forall y1 : nat, (@IN nat y1 (dotdot x0 y0)) = ((Peano.le x0 y1) /\ (Peano.le y1 y0)).
Definition term53 := forall y0 : nat, True.
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) := fun y0 : nat => (@IN nat y0 (dotdot x0 x1)) -> real_le (x2 y0) (x3 y0).
Definition term18 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_le (@sum a0 x1 x0) (@sum a0 x1 x2).
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) (x4 : Prop) := ((forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x1)) -> real_le (x2 y0) (x3 y0)) -> (real_le (@sum nat (dotdot x0 x1) x2) (@sum nat (dotdot x0 x1) x3)) = x4) -> ((forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x1)) -> real_le (x2 y0) (x3 y0)) -> real_le (@sum nat (dotdot x0 x1) x2) (@sum nat (dotdot x0 x1) x3)) = ((forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x1)) -> real_le (x2 y0) (x3 y0)) -> x4).
Definition term51 := fun y0 : nat => True.
Definition term3 (x0 : nat) (x1 : nat) := forall y0 : nat, (@IN nat y0 (dotdot x0 x1)) = ((Peano.le x0 y0) /\ (Peano.le y0 x1)).
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) (x4 : nat) (x5 : Prop) := forall y0 : Prop, ((@IN nat x4 (dotdot x0 x1)) = x5) -> (x5 -> (real_le (x2 x4) (x3 x4)) = y0) -> ((@IN nat x4 (dotdot x0 x1)) -> real_le (x2 x4) (x3 x4)) = (x5 -> y0).
Definition term26 (x0 : nat -> real) (x1 : nat) (x2 : nat) (x3 : nat -> real) (x4 : Prop) := forall y0 : Prop, ((forall y1 : nat, ((Peano.le x1 y1) /\ (Peano.le y1 x2)) -> real_le (x0 y1) (x3 y1)) = x4) -> (x4 -> (real_le (@sum nat (dotdot x1 x2) x0) (@sum nat (dotdot x1 x2) x3)) = y0) -> ((forall y1 : nat, ((Peano.le x1 y1) /\ (Peano.le y1 x2)) -> real_le (x0 y1) (x3 y1)) -> real_le (@sum nat (dotdot x1 x2) x0) (@sum nat (dotdot x1 x2) x3)) = (x4 -> y0).
Definition term20 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) (x4 : nat) := forall y0 : Prop, forall y1 : Prop, ((@IN nat x4 (dotdot x0 x1)) = y0) -> (y0 -> (real_le (x2 x4) (x3 x4)) = y1) -> ((@IN nat x4 (dotdot x0 x1)) -> real_le (x2 x4) (x3 x4)) = (y0 -> y1).
Definition term22 (x0 : nat -> real) (x1 : nat) (x2 : nat) (x3 : nat -> real) := forall y0 : Prop, forall y1 : Prop, ((forall y2 : nat, ((Peano.le x1 y2) /\ (Peano.le y2 x2)) -> real_le (x0 y2) (x3 y2)) = y0) -> (y0 -> (real_le (@sum nat (dotdot x1 x2) x0) (@sum nat (dotdot x1 x2) x3)) = y1) -> ((forall y2 : nat, ((Peano.le x1 y2) /\ (Peano.le y2 x2)) -> real_le (x0 y2) (x3 y2)) -> real_le (@sum nat (dotdot x1 x2) x0) (@sum nat (dotdot x1 x2) x3)) = (y0 -> y1).
Definition term21 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term32 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) (x4 : nat) := ((Peano.le x0 x4) /\ (Peano.le x4 x1)) -> real_le (x2 x4) (x3 x4).
Definition term12 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> real, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (forall y2 : a0, (@IN a0 y2 y1) -> real_le (x0 y2) (y0 y2))) -> real_le (@sum a0 y1 x0) (@sum a0 y1 y0).
Definition term10 (x0 : nat) (x1 : nat) := @FINITE nat (dotdot x0 x1).
Definition term27 (x0 : nat -> real) (x1 : nat) (x2 : nat) (x3 : nat -> real) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => ((forall y1 : nat, ((Peano.le x1 y1) /\ (Peano.le y1 x2)) -> real_le (x0 y1) (x3 y1)) = x4) -> (x4 -> (real_le (@sum nat (dotdot x1 x2) x0) (@sum nat (dotdot x1 x2) x3)) = y0) -> ((forall y1 : nat, ((Peano.le x1 y1) /\ (Peano.le y1 x2)) -> real_le (x0 y1) (x3 y1)) -> real_le (@sum nat (dotdot x1 x2) x0) (@sum nat (dotdot x1 x2) x3)) = (x4 -> y0)) x5.
Definition term37 (x0 : nat) (x1 : nat) := and (@FINITE nat (dotdot x0 x1)).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) (x4 : Prop) := ((forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x1)) -> real_le (x2 y0) (x3 y0)) = (forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x1)) -> real_le (x2 y0) (x3 y0))) -> ((forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x1)) -> real_le (x2 y0) (x3 y0)) -> (real_le (@sum nat (dotdot x0 x1) x2) (@sum nat (dotdot x0 x1) x3)) = x4) -> ((forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x1)) -> real_le (x2 y0) (x3 y0)) -> real_le (@sum nat (dotdot x0 x1) x2) (@sum nat (dotdot x0 x1) x3)) = ((forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x1)) -> real_le (x2 y0) (x3 y0)) -> x4).
Definition term62 (x0 : nat -> real) (x1 : nat) (x2 : nat -> real) := forall y0 : nat, (forall y1 : nat, ((Peano.le x1 y1) /\ (Peano.le y1 y0)) -> real_le (x0 y1) (x2 y1)) -> real_le (@sum nat (dotdot x1 y0) x0) (@sum nat (dotdot x1 y0) x2).
Definition term66 := fun y0 : nat -> real => True.
Definition term57 (x0 : nat -> real) (x1 : nat) (x2 : nat) (x3 : nat -> real) := (forall y0 : nat, ((Peano.le x1 y0) /\ (Peano.le y0 x2)) -> real_le (x0 y0) (x3 y0)) -> (real_le (@sum nat (dotdot x1 x2) x0) (@sum nat (dotdot x1 x2) x3)) = True.
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (@IN nat y0 (dotdot x0 x1)) = ((Peano.le x0 y0) /\ (Peano.le y0 x1))) x2.
Definition term16 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := ((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> real_le (x0 y0) (x2 y0))) -> real_le (@sum a0 x1 x0) (@sum a0 x1 x2).
Definition term69 (x0 : Prop) := forall y0 : nat -> real, x0.
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> real) := (@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> real_le (x1 y0) (x2 y0)).
Definition term70 := fun y0 : nat -> real => forall y1 : nat -> real, forall y2 : nat, forall y3 : nat, (forall y4 : nat, ((Peano.le y2 y4) /\ (Peano.le y4 y3)) -> real_le (y0 y4) (y1 y4)) -> real_le (@sum nat (dotdot y2 y3) y0) (@sum nat (dotdot y2 y3) y1).
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) := forall y0 : nat, (@IN nat y0 (dotdot x0 x1)) -> real_le (x2 y0) (x3 y0).
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) := forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x1)) -> real_le (x2 y0) (x3 y0).
Definition term7 (x0 : nat) := (fun y0 : nat => forall y1 : nat, @FINITE nat (dotdot y0 y1)) x0.
Definition term58 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) := ((forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x1)) -> real_le (x2 y0) (x3 y0)) -> (real_le (@sum nat (dotdot x0 x1) x2) (@sum nat (dotdot x0 x1) x3)) = True) -> ((forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x1)) -> real_le (x2 y0) (x3 y0)) -> real_le (@sum nat (dotdot x0 x1) x2) (@sum nat (dotdot x0 x1) x3)) = ((forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x1)) -> real_le (x2 y0) (x3 y0)) -> True).
Definition term55 (x0 : Prop) := forall y0 : nat, x0.
Definition term35 (x0 : nat -> real) (x1 : nat -> Prop) (x2 : nat -> real) := ((@FINITE nat x1) /\ (forall y0 : nat, (@IN nat y0 x1) -> real_le (x0 y0) (x2 y0))) -> (real_le (@sum nat x1 x0) (@sum nat x1 x2)) = True.
Definition term34 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) (x2 : a0 -> real) := ((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> real_le (x0 y0) (x2 y0))) -> (real_le (@sum a0 x1 x0) (@sum a0 x1 x2)) = True.
Definition term49 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x0 x1) /\ (Peano.le x1 x2)) -> True.
Definition term33 (x0 : nat -> real) (x1 : nat -> real) (x2 : nat) := real_le (x0 x2) (x1 x2).
Definition term14 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> real) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (forall y1 : a0, (@IN a0 y1 y0) -> real_le (x0 y1) (x1 y1))) -> real_le (@sum a0 y0 x0) (@sum a0 y0 x1).
Definition term25 (x0 : nat -> real) (x1 : nat) (x2 : nat) (x3 : nat -> real) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((forall y2 : nat, ((Peano.le x1 y2) /\ (Peano.le y2 x2)) -> real_le (x0 y2) (x3 y2)) = y0) -> (y0 -> (real_le (@sum nat (dotdot x1 x2) x0) (@sum nat (dotdot x1 x2) x3)) = y1) -> ((forall y2 : nat, ((Peano.le x1 y2) /\ (Peano.le y2 x2)) -> real_le (x0 y2) (x3 y2)) -> real_le (@sum nat (dotdot x1 x2) x0) (@sum nat (dotdot x1 x2) x3)) = (y0 -> y1)) x4.
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) (x4 : nat) := (@IN nat x4 (dotdot x0 x1)) -> real_le (x2 x4) (x3 x4).
Definition term63 (x0 : nat -> real) (x1 : nat -> real) := fun y0 : nat => forall y1 : nat, (forall y2 : nat, ((Peano.le y0 y2) /\ (Peano.le y2 y1)) -> real_le (x0 y2) (x1 y2)) -> real_le (@sum nat (dotdot y0 y1) x0) (@sum nat (dotdot y0 y1) x1).
Definition term46 (x0 : nat) (x1 : nat) := and (Peano.le x0 x1).
