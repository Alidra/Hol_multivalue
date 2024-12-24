Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat) := @eq real (@sum nat (dotdot x0 x1) (@o nat nat real x2 (fun y0 : nat => Nat.add y0 x3))).
Definition term7 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.add x0 y0) = (Nat.add x1 y0)) = (x0 = x1).
Definition term72 (x0 : nat) (x1 : nat -> real) (x2 : nat) := fun y0 : nat => (@sum nat (dotdot x0 y0) (@o nat nat real x1 (fun y1 : nat => Nat.add y1 x2))) = (@sum nat (dotdot x0 y0) (fun y1 : nat => x1 (Nat.add y1 x2))).
Definition term31 (x0 : nat) := fun y0 : nat => Nat.add y0 x0.
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := @sum nat (dotdot (Nat.add x0 x2) (Nat.add x1 x2)).
Definition term56 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (((@IN nat x3 (dotdot x1 x2)) /\ ((@IN nat x4 (dotdot x1 x2)) /\ (x3 = x4))) -> (x3 = x4) = True) -> (((@IN nat x3 (dotdot x1 x2)) /\ ((@IN nat x4 (dotdot x1 x2)) /\ (((fun y0 : nat => Nat.add y0 x0) x3) = ((fun y0 : nat => Nat.add y0 x0) x4)))) -> x3 = x4) = (((@IN nat x3 (dotdot x1 x2)) /\ ((@IN nat x4 (dotdot x1 x2)) /\ (x3 = x4))) -> True).
Definition term55 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((@IN nat x2 (dotdot x0 x1)) /\ ((@IN nat x3 (dotdot x0 x1)) /\ (x2 = x3))) -> (x2 = x3) = True.
Definition term18 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (dotdot (Nat.add y0 y2) (Nat.add y1 y2)) = (@IMAGE nat nat (fun y3 : nat => Nat.add y3 y2) (dotdot y0 y1))) x0.
Definition term4 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.add y0 y2) = (Nat.add y1 y2)) = (y0 = y1)) x0.
Definition term50 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (@IN nat x4 (dotdot x0 x1)) /\ (((fun y0 : nat => Nat.add y0 x3) x2) = ((fun y0 : nat => Nat.add y0 x3) x4)).
Definition term48 (x0 : nat) (x1 : nat) := @eq nat (Nat.add x0 x1).
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.add x0 y0) = (Nat.add x1 y0)) = (x0 = x1)) x2.
Definition term63 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : Prop) (x6 : Prop) := (((@IN nat x3 (dotdot x0 x1)) /\ ((@IN nat x4 (dotdot x0 x1)) /\ (((fun y0 : nat => Nat.add y0 x2) x3) = ((fun y0 : nat => Nat.add y0 x2) x4)))) = x5) -> (x5 -> (x3 = x4) = x6) -> (((@IN nat x3 (dotdot x0 x1)) /\ ((@IN nat x4 (dotdot x0 x1)) /\ (((fun y0 : nat => Nat.add y0 x2) x3) = ((fun y0 : nat => Nat.add y0 x2) x4)))) -> x3 = x4) = (x5 -> x6).
Definition term93 (x0 : nat) (x1 : nat) := @sum nat (dotdot x0 x1).
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (dotdot (Nat.add x0 y0) (Nat.add x1 y0)) = (@IMAGE nat nat (fun y1 : nat => Nat.add y1 y0) (dotdot x0 x1))) x2.
Definition term80 (x0 : nat) := fun y0 : nat -> real => forall y1 : nat, forall y2 : nat, (@sum nat (dotdot y1 y2) (@o nat nat real y0 (fun y3 : nat => Nat.add y3 x0))) = (@sum nat (dotdot y1 y2) (fun y3 : nat => y0 (Nat.add y3 x0))).
Definition term79 (x0 : nat) := fun y0 : nat -> real => forall y1 : nat, forall y2 : nat, (@sum nat (dotdot (Nat.add y1 x0) (Nat.add y2 x0)) y0) = (@sum nat (dotdot y1 y2) (fun y3 : nat => y0 (Nat.add y3 x0))).
Definition term76 (x0 : nat -> real) (x1 : nat) := fun y0 : nat => forall y1 : nat, (@sum nat (dotdot y0 y1) (@o nat nat real x0 (fun y2 : nat => Nat.add y2 x1))) = (@sum nat (dotdot y0 y1) (fun y2 : nat => x0 (Nat.add y2 x1))).
Definition term75 (x0 : nat -> real) (x1 : nat) := fun y0 : nat => forall y1 : nat, (@sum nat (dotdot (Nat.add y0 x1) (Nat.add y1 x1)) x0) = (@sum nat (dotdot y0 y1) (fun y2 : nat => x0 (Nat.add y2 x1))).
Definition term17 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> real) (x2 : a1 -> a0) := @sum a1 x0 (@o a1 a0 real x1 x2).
Definition term29 (x0 : nat -> Prop) (x1 : nat -> real) (x2 : nat -> nat) := (forall y0 : nat, forall y1 : nat, ((@IN nat y0 x0) /\ ((@IN nat y1 x0) /\ ((x2 y0) = (x2 y1)))) -> y0 = y1) -> (@sum nat (@IMAGE nat nat x2 x0) x1) = (@sum nat x0 (@o nat nat real x1 x2)).
Definition term82 (x0 : nat) := forall y0 : nat -> real, forall y1 : nat, forall y2 : nat, (@sum nat (dotdot y1 y2) (@o nat nat real y0 (fun y3 : nat => Nat.add y3 x0))) = (@sum nat (dotdot y1 y2) (fun y3 : nat => y0 (Nat.add y3 x0))).
Definition term81 (x0 : nat) := forall y0 : nat -> real, forall y1 : nat, forall y2 : nat, (@sum nat (dotdot (Nat.add y1 x0) (Nat.add y2 x0)) y0) = (@sum nat (dotdot y1 y2) (fun y3 : nat => y0 (Nat.add y3 x0))).
Definition term96 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat) := @eq Prop ((fun y0 : Prop => y0 = True) ((@sum nat (dotdot x0 x1) (fun y0 : nat => x2 (Nat.add y0 x3))) = (@sum nat (dotdot x0 x1) (fun y0 : nat => x2 (Nat.add y0 x3))))).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> real) (x2 : a1 -> a0) := (forall y0 : a1, forall y1 : a1, ((@IN a1 y0 x0) /\ ((@IN a1 y1 x0) /\ ((x2 y0) = (x2 y1)))) -> y0 = y1) -> (@sum a0 (@IMAGE a1 a0 x2 x0) x1) = (@sum a1 x0 (@o a1 a0 real x1 x2)).
Definition term87 (x0 : nat -> real) (x1 : nat -> nat) := fun y0 : nat => x0 (x1 y0).
Definition term20 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (dotdot (Nat.add x0 y1) (Nat.add y0 y1)) = (@IMAGE nat nat (fun y2 : nat => Nat.add y2 y1) (dotdot x0 y0))) x1.
Definition term6 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add x0 y1) = (Nat.add y0 y1)) = (x0 = y0)) x1.
Definition term11 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a1 -> Prop, (forall y2 : a1, forall y3 : a1, ((@IN a1 y2 y1) /\ ((@IN a1 y3 y1) /\ ((x0 y2) = (x0 y3)))) -> y2 = y3) -> (@sum a0 (@IMAGE a1 a0 x0 y1) y0) = (@sum a1 y1 (@o a1 a0 real y0 x0))) x1.
Definition term59 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := fun y0 : nat => ((@IN nat x3 (dotdot x0 x1)) /\ ((@IN nat y0 (dotdot x0 x1)) /\ (((fun y1 : nat => Nat.add y1 x2) x3) = ((fun y1 : nat => Nat.add y1 x2) y0)))) -> x3 = y0.
Definition term65 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => forall y1 : nat, ((@IN nat y0 (dotdot x0 x1)) /\ ((@IN nat y1 (dotdot x0 x1)) /\ (((fun y2 : nat => Nat.add y2 x2) y0) = ((fun y2 : nat => Nat.add y2 x2) y1)))) -> y0 = y1.
Definition term95 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat) := (fun y0 : Prop => y0 = True) ((@sum nat (dotdot x0 x1) (fun y0 : nat => x2 (Nat.add y0 x3))) = (@sum nat (dotdot x0 x1) (fun y0 : nat => x2 (Nat.add y0 x3)))).
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat) := @sum nat (dotdot x0 x1) (fun y0 : nat => x2 (Nat.add y0 x3)).
Definition term84 := fun y0 : nat => forall y1 : nat -> real, forall y2 : nat, forall y3 : nat, (@sum nat (dotdot y2 y3) (@o nat nat real y1 (fun y4 : nat => Nat.add y4 y0))) = (@sum nat (dotdot y2 y3) (fun y4 : nat => y1 (Nat.add y4 y0))).
Definition term83 := fun y0 : nat => forall y1 : nat -> real, forall y2 : nat, forall y3 : nat, (@sum nat (dotdot (Nat.add y2 y0) (Nat.add y3 y0)) y1) = (@sum nat (dotdot y2 y3) (fun y4 : nat => y1 (Nat.add y4 y0))).
Definition term16 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1 -> Prop) (x2 : a0 -> real) := @sum a0 (@IMAGE a1 a0 x0 x1) x2.
Definition term97 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat) := @eq Prop (((@sum nat (dotdot x0 x1) (fun y0 : nat => x2 (Nat.add y0 x3))) = (@sum nat (dotdot x0 x1) (fun y0 : nat => x2 (Nat.add y0 x3)))) = True).
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : Prop) (x6 : Prop) := (fun y0 : Prop => (((@IN nat x3 (dotdot x0 x1)) /\ ((@IN nat x4 (dotdot x0 x1)) /\ (((fun y1 : nat => Nat.add y1 x2) x3) = ((fun y1 : nat => Nat.add y1 x2) x4)))) = x5) -> (x5 -> (x3 = x4) = y0) -> (((@IN nat x3 (dotdot x0 x1)) /\ ((@IN nat x4 (dotdot x0 x1)) /\ (((fun y1 : nat => Nat.add y1 x2) x3) = ((fun y1 : nat => Nat.add y1 x2) x4)))) -> x3 = x4) = (x5 -> y0)) x6.
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat -> real) := @sum nat (dotdot (Nat.add x0 x2) (Nat.add x1 x2)) x3.
Definition term32 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat -> real) := @eq real (@sum nat (dotdot (Nat.add x0 x2) (Nat.add x1 x2)) x3).
Definition term44 (x0 : nat) (x1 : nat) := (fun y0 : nat => Nat.add y0 x0) x1.
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((@IN nat x3 (dotdot x0 x1)) /\ ((@IN nat x4 (dotdot x0 x1)) /\ (((fun y2 : nat => Nat.add y2 x2) x3) = ((fun y2 : nat => Nat.add y2 x2) x4)))) = y0) -> (y0 -> (x3 = x4) = y1) -> (((@IN nat x3 (dotdot x0 x1)) /\ ((@IN nat x4 (dotdot x0 x1)) /\ (((fun y2 : nat => Nat.add y2 x2) x3) = ((fun y2 : nat => Nat.add y2 x2) x4)))) -> x3 = x4) = (y0 -> y1)) x5.
Definition term51 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (@IN nat x3 (dotdot x0 x1)) /\ (x2 = x3).
Definition term41 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term99 := forall y0 : nat -> real, True.
Definition term86 := forall y0 : nat, forall y1 : nat -> real, forall y2 : nat, forall y3 : nat, (@sum nat (dotdot y2 y3) (@o nat nat real y1 (fun y4 : nat => Nat.add y4 y0))) = (@sum nat (dotdot y2 y3) (fun y4 : nat => y1 (Nat.add y4 y0))).
Definition term85 := forall y0 : nat, forall y1 : nat -> real, forall y2 : nat, forall y3 : nat, (@sum nat (dotdot (Nat.add y2 y0) (Nat.add y3 y0)) y1) = (@sum nat (dotdot y2 y3) (fun y4 : nat => y1 (Nat.add y4 y0))).
Definition term78 (x0 : nat -> real) (x1 : nat) := forall y0 : nat, forall y1 : nat, (@sum nat (dotdot y0 y1) (@o nat nat real x0 (fun y2 : nat => Nat.add y2 x1))) = (@sum nat (dotdot y0 y1) (fun y2 : nat => x0 (Nat.add y2 x1))).
Definition term77 (x0 : nat -> real) (x1 : nat) := forall y0 : nat, forall y1 : nat, (@sum nat (dotdot (Nat.add y0 x1) (Nat.add y1 x1)) x0) = (@sum nat (dotdot y0 y1) (fun y2 : nat => x0 (Nat.add y2 x1))).
Definition term66 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, forall y1 : nat, ((@IN nat y0 (dotdot x0 x1)) /\ ((@IN nat y1 (dotdot x0 x1)) /\ (((fun y2 : nat => Nat.add y2 x2) y0) = ((fun y2 : nat => Nat.add y2 x2) y1)))) -> y0 = y1.
Definition term19 (x0 : nat) := forall y0 : nat, forall y1 : nat, (dotdot (Nat.add x0 y1) (Nat.add y0 y1)) = (@IMAGE nat nat (fun y2 : nat => Nat.add y2 y1) (dotdot x0 y0)).
Definition term5 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.add x0 y1) = (Nat.add y0 y1)) = (x0 = y0).
Definition term89 (x0 : nat -> real) (x1 : nat) := fun y0 : nat => x0 ((fun y1 : nat => Nat.add y1 x1) y0).
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := dotdot (Nat.add x0 x2) (Nat.add x1 x2).
Definition term90 (x0 : nat -> real) (x1 : nat) (x2 : nat) := x0 ((fun y0 : nat => Nat.add y0 x1) x2).
Definition term54 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : Prop) := (((@IN nat x3 (dotdot x1 x2)) /\ ((@IN nat x4 (dotdot x1 x2)) /\ (x3 = x4))) -> (x3 = x4) = x5) -> (((@IN nat x3 (dotdot x1 x2)) /\ ((@IN nat x4 (dotdot x1 x2)) /\ (((fun y0 : nat => Nat.add y0 x0) x3) = ((fun y0 : nat => Nat.add y0 x0) x4)))) -> x3 = x4) = (((@IN nat x3 (dotdot x1 x2)) /\ ((@IN nat x4 (dotdot x1 x2)) /\ (x3 = x4))) -> x5).
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat -> real) := @sum nat (@IMAGE nat nat (fun y0 : nat => Nat.add y0 x0) (dotdot x1 x2)) x3.
Definition term42 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term62 := forall y0 : nat, True.
Definition term21 (x0 : nat) (x1 : nat) := forall y0 : nat, (dotdot (Nat.add x0 y0) (Nat.add x1 y0)) = (@IMAGE nat nat (fun y1 : nat => Nat.add y1 y0) (dotdot x0 x1)).
Definition term60 := fun y0 : nat => True.
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := @sum nat (@IMAGE nat nat (fun y0 : nat => Nat.add y0 x0) (dotdot x1 x2)).
Definition term73 (x0 : nat) (x1 : nat -> real) (x2 : nat) := forall y0 : nat, (@sum nat (dotdot (Nat.add x0 x2) (Nat.add y0 x2)) x1) = (@sum nat (dotdot x0 y0) (fun y1 : nat => x1 (Nat.add y1 x2))).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0 -> real) (x1 : a1 -> a0) := forall y0 : a1 -> Prop, (forall y1 : a1, forall y2 : a1, ((@IN a1 y1 y0) /\ ((@IN a1 y2 y0) /\ ((x1 y1) = (x1 y2)))) -> y1 = y2) -> (@sum a0 (@IMAGE a1 a0 x1 y0) x0) = (@sum a1 y0 (@o a1 a0 real x0 x1)).
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : Prop) := forall y0 : Prop, (((@IN nat x3 (dotdot x0 x1)) /\ ((@IN nat x4 (dotdot x0 x1)) /\ (((fun y1 : nat => Nat.add y1 x2) x3) = ((fun y1 : nat => Nat.add y1 x2) x4)))) = x5) -> (x5 -> (x3 = x4) = y0) -> (((@IN nat x3 (dotdot x0 x1)) /\ ((@IN nat x4 (dotdot x0 x1)) /\ (((fun y1 : nat => Nat.add y1 x2) x3) = ((fun y1 : nat => Nat.add y1 x2) x4)))) -> x3 = x4) = (x5 -> y0).
Definition term33 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term53 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) (x5 : Prop) := (((@IN nat x3 (dotdot x1 x2)) /\ ((@IN nat x4 (dotdot x1 x2)) /\ (((fun y0 : nat => Nat.add y0 x0) x3) = ((fun y0 : nat => Nat.add y0 x0) x4)))) = ((@IN nat x3 (dotdot x1 x2)) /\ ((@IN nat x4 (dotdot x1 x2)) /\ (x3 = x4)))) -> (((@IN nat x3 (dotdot x1 x2)) /\ ((@IN nat x4 (dotdot x1 x2)) /\ (x3 = x4))) -> (x3 = x4) = x5) -> (((@IN nat x3 (dotdot x1 x2)) /\ ((@IN nat x4 (dotdot x1 x2)) /\ (((fun y0 : nat => Nat.add y0 x0) x3) = ((fun y0 : nat => Nat.add y0 x0) x4)))) -> x3 = x4) = (((@IN nat x3 (dotdot x1 x2)) /\ ((@IN nat x4 (dotdot x1 x2)) /\ (x3 = x4))) -> x5).
Definition term0 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) := (fun y0 : a1 -> a2 => forall y1 : a0 -> a1, (@o a0 a1 a2 y0 y1) = (fun y2 : a0 => y0 (y1 y2))) x0.
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := forall y0 : Prop, forall y1 : Prop, (((@IN nat x3 (dotdot x0 x1)) /\ ((@IN nat x4 (dotdot x0 x1)) /\ (((fun y2 : nat => Nat.add y2 x2) x3) = ((fun y2 : nat => Nat.add y2 x2) x4)))) = y0) -> (y0 -> (x3 = x4) = y1) -> (((@IN nat x3 (dotdot x0 x1)) /\ ((@IN nat x4 (dotdot x0 x1)) /\ (((fun y2 : nat => Nat.add y2 x2) x3) = ((fun y2 : nat => Nat.add y2 x2) x4)))) -> x3 = x4) = (y0 -> y1).
Definition term34 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term61 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := forall y0 : nat, ((@IN nat x3 (dotdot x0 x1)) /\ ((@IN nat y0 (dotdot x0 x1)) /\ (((fun y1 : nat => Nat.add y1 x2) x3) = ((fun y1 : nat => Nat.add y1 x2) y0)))) -> x3 = y0.
Definition term10 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := forall y0 : a0 -> real, forall y1 : a1 -> Prop, (forall y2 : a1, forall y3 : a1, ((@IN a1 y2 y1) /\ ((@IN a1 y3 y1) /\ ((x0 y2) = (x0 y3)))) -> y2 = y3) -> (@sum a0 (@IMAGE a1 a0 x0 y1) y0) = (@sum a1 y1 (@o a1 a0 real y0 x0)).
Definition term74 (x0 : nat) (x1 : nat -> real) (x2 : nat) := forall y0 : nat, (@sum nat (dotdot x0 y0) (@o nat nat real x1 (fun y1 : nat => Nat.add y1 x2))) = (@sum nat (dotdot x0 y0) (fun y1 : nat => x1 (Nat.add y1 x2))).
Definition term88 (x0 : nat -> real) (x1 : nat) := @o nat nat real x0 (fun y0 : nat => Nat.add y0 x1).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0 -> real) (x1 : a1 -> a0) (x2 : a1 -> Prop) := (fun y0 : a1 -> Prop => (forall y1 : a1, forall y2 : a1, ((@IN a1 y1 y0) /\ ((@IN a1 y2 y0) /\ ((x1 y1) = (x1 y2)))) -> y1 = y2) -> (@sum a0 (@IMAGE a1 a0 x1 y0) x0) = (@sum a1 y0 (@o a1 a0 real x0 x1))) x2.
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat) := (forall y0 : nat, forall y1 : nat, ((@IN nat y0 (dotdot x0 x1)) /\ ((@IN nat y1 (dotdot x0 x1)) /\ (((fun y2 : nat => Nat.add y2 x3) y0) = ((fun y2 : nat => Nat.add y2 x3) y1)))) -> y0 = y1) -> (@sum nat (@IMAGE nat nat (fun y0 : nat => Nat.add y0 x3) (dotdot x0 x1)) x2) = (@sum nat (dotdot x0 x1) (@o nat nat real x2 (fun y0 : nat => Nat.add y0 x3))).
Definition term52 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (@IN nat x2 (dotdot x0 x1)) /\ ((@IN nat x3 (dotdot x0 x1)) /\ (x2 = x3)).
Definition term98 := fun y0 : nat -> real => True.
Definition term57 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := ((@IN nat x3 (dotdot x0 x1)) /\ ((@IN nat x4 (dotdot x0 x1)) /\ (((fun y0 : nat => Nat.add y0 x2) x3) = ((fun y0 : nat => Nat.add y0 x2) x4)))) -> x3 = x4.
Definition term46 (x0 : nat) (x1 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => Nat.add y1 x0) y0) x1).
Definition term100 (x0 : Prop) := forall y0 : nat -> real, x0.
Definition term15 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1 -> a0) := forall y0 : a1, forall y1 : a1, ((@IN a1 y0 x0) /\ ((@IN a1 y1 x0) /\ ((x1 y0) = (x1 y1)))) -> y0 = y1.
Definition term1 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) := forall y0 : a0 -> a1, (@o a0 a1 a2 x0 y0) = (fun y1 : a0 => x0 (y0 y1)).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) := (fun y0 : a1 -> a0 => forall y1 : a0 -> real, forall y2 : a1 -> Prop, (forall y3 : a1, forall y4 : a1, ((@IN a1 y3 y2) /\ ((@IN a1 y4 y2) /\ ((y0 y3) = (y0 y4)))) -> y3 = y4) -> (@sum a0 (@IMAGE a1 a0 y0 y2) y1) = (@sum a1 y2 (@o a1 a0 real y1 y0))) x0.
Definition term2 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => (@o a0 a1 a2 x0 y0) = (fun y1 : a0 => x0 (y0 y1))) x1.
Definition term67 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat) := @sum nat (dotdot x0 x1) (@o nat nat real x2 (fun y0 : nat => Nat.add y0 x3)).
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := @IMAGE nat nat (fun y0 : nat => Nat.add y0 x0) (dotdot x1 x2).
Definition term64 (x0 : Prop) := forall y0 : nat, x0.
Definition term45 (x0 : nat) := fun y0 : nat => (fun y1 : nat => Nat.add y1 x0) y0.
Definition term94 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat) := @eq real (@sum nat (dotdot x0 x1) (fun y0 : nat => x2 (Nat.add y0 x3))).
Definition term91 (x0 : nat -> real) (x1 : nat) (x2 : nat) := x0 (Nat.add x1 x2).
Definition term71 (x0 : nat) (x1 : nat -> real) (x2 : nat) := fun y0 : nat => (@sum nat (dotdot (Nat.add x0 x2) (Nat.add y0 x2)) x1) = (@sum nat (dotdot x0 y0) (fun y1 : nat => x1 (Nat.add y1 x2))).
Definition term47 (x0 : nat) (x1 : nat) := @eq nat ((fun y0 : nat => Nat.add y0 x0) x1).
Definition term3 (a0 : Type') (a1 : Type') (a2 : Type') (x0 : a1 -> a2) (x1 : a0 -> a1) := fun y0 : a0 => x0 (x1 y0).
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : nat) := (@IN nat x2 (dotdot x0 x1)) /\ ((@IN nat x4 (dotdot x0 x1)) /\ (((fun y0 : nat => Nat.add y0 x3) x2) = ((fun y0 : nat => Nat.add y0 x3) x4))).
Definition term49 (x0 : nat) (x1 : nat) (x2 : nat) := and (@IN nat x0 (dotdot x1 x2)).
Definition term43 (x0 : nat) (x1 : nat) := (fun y0 : nat => (fun y1 : nat => Nat.add y1 x0) y0) x1.
Definition term58 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((@IN nat x2 (dotdot x0 x1)) /\ ((@IN nat x3 (dotdot x0 x1)) /\ (x2 = x3))) -> True.
Definition term92 (x0 : nat -> real) (x1 : nat) := fun y0 : nat => x0 (Nat.add y0 x1).
