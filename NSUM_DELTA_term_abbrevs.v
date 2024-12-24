Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term37 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : a0) := @COND nat (x2 = x0) ((fun y0 : a0 => x1) x2) (@neutral nat Nat.add).
Definition term42 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0) := @COND nat (@IN a0 x2 x0) ((fun y0 : a0 => x1) x2).
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1400 a0) := (@monoidal a0 x0) -> forall y0 : a1 -> a0, forall y1 : a1, forall y2 : a1 -> Prop, (@iterate a0 a1 x0 y2 (fun y3 : a1 => @COND a0 (y3 = y1) (y0 y3) (@neutral a0 x0))) = (@COND a0 (@IN a1 y1 y2) (y0 y1) (@neutral a0 x0)).
Definition term33 (a0 : Type') (x0 : nat) := fun y0 : a0 => x0.
Definition term8 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1) (x2 : a1 -> a0) (x3 : type1400 a0) := @iterate a0 a1 x3 x0 (fun y0 : a1 => @COND a0 (y0 = x1) (x2 y0) (@neutral a0 x3)).
Definition term49 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term48 (a0 : Type') := forall y0 : a0, True.
Definition term52 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := @iterate nat a0 Nat.add x0 (fun y0 : a0 => @COND nat (y0 = x1) x2 (@neutral nat Nat.add)).
Definition term44 := imp (@monoidal nat Nat.add).
Definition term45 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := (@monoidal nat Nat.add) -> (@iterate nat a0 Nat.add x1 (fun y0 : a0 => @COND nat (y0 = x0) x2 (@neutral nat Nat.add))) = (@COND nat (@IN a0 x0 x1) x2 (@neutral nat Nat.add)).
Definition term15 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := @nsum a0 x0 (fun y0 : a0 => @COND nat (y0 = x1) x2 (NUMERAL 0)).
Definition term35 (a0 : Type') (x0 : a0) (x1 : a0) := @COND nat (x0 = x1).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1 -> a0) (x2 : a1) (x3 : type1400 a0) := @COND a0 (@IN a1 x2 x0) (x1 x2) (@neutral a0 x3).
Definition term32 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0) := (@monoidal nat Nat.add) -> (@iterate nat a0 Nat.add x0 (fun y0 : a0 => @COND nat (y0 = x2) ((fun y1 : a0 => x1) y0) (@neutral nat Nat.add))) = (@COND nat (@IN a0 x2 x0) ((fun y0 : a0 => x1) x2) (@neutral nat Nat.add)).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : type1400 a0) (x2 : a1) := (fun y0 : a1 => forall y1 : a1 -> Prop, (@iterate a0 a1 x1 y1 (fun y2 : a1 => @COND a0 (y2 = y0) (x0 y2) (@neutral a0 x1))) = (@COND a0 (@IN a1 y0 y1) (x0 y0) (@neutral a0 x1))) x2.
Definition term10 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : nat) := @COND nat (x0 = x1) x2.
Definition term31 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : type1606) := (@monoidal nat x3) -> (@iterate nat a0 x3 x0 (fun y0 : a0 => @COND nat (y0 = x2) (x1 y0) (@neutral nat x3))) = (@COND nat (@IN a0 x2 x0) (x1 x2) (@neutral nat x3)).
Definition term30 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1 -> a0) (x2 : a1) (x3 : type1400 a0) := (@monoidal a0 x3) -> (@iterate a0 a1 x3 x0 (fun y0 : a1 => @COND a0 (y0 = x2) (x1 y0) (@neutral a0 x3))) = (@COND a0 (@IN a1 x2 x0) (x1 x2) (@neutral a0 x3)).
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := @iterate nat a0 Nat.add x0 (fun y0 : a0 => @COND nat (y0 = x1) ((fun y1 : a0 => x2) y0) (@neutral nat Nat.add)).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := forall y0 : a0, (@iterate nat a0 Nat.add x0 (fun y1 : a0 => @COND nat (y1 = y0) x1 (@neutral nat Nat.add))) = (@COND nat (@IN a0 y0 x0) x1 (@neutral nat Nat.add)).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := forall y0 : a0, (@nsum a0 x0 (fun y1 : a0 => @COND nat (y1 = y0) x1 (NUMERAL 0))) = (@COND nat (@IN a0 y0 x0) x1 (NUMERAL 0)).
Definition term43 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0) := @COND nat (@IN a0 x2 x0) ((fun y0 : a0 => x1) x2) (@neutral nat Nat.add).
Definition term27 (a0 : Type') (x0 : nat) := fun y0 : a0 -> Prop => forall y1 : a0, (@iterate nat a0 Nat.add y0 (fun y2 : a0 => @COND nat (y2 = y1) x0 (@neutral nat Nat.add))) = (@COND nat (@IN a0 y1 y0) x0 (@neutral nat Nat.add)).
Definition term26 (a0 : Type') (x0 : nat) := fun y0 : a0 -> Prop => forall y1 : a0, (@nsum a0 y0 (fun y2 : a0 => @COND nat (y2 = y1) x0 (NUMERAL 0))) = (@COND nat (@IN a0 y1 y0) x0 (NUMERAL 0)).
Definition term0 (a0 : Type') (a1 : Type') (x0 : type1400 a0) := (fun y0 : type1400 a0 => (@monoidal a0 y0) -> forall y1 : a1 -> a0, forall y2 : a1, forall y3 : a1 -> Prop, (@iterate a0 a1 y0 y3 (fun y4 : a1 => @COND a0 (y4 = y2) (y1 y4) (@neutral a0 y0))) = (@COND a0 (@IN a1 y2 y3) (y1 y2) (@neutral a0 y0))) x0.
Definition term34 (a0 : Type') (x0 : nat) (x1 : a0) := (fun y0 : a0 => x0) x1.
Definition term47 (a0 : Type') := fun y0 : a0 => True.
Definition term4 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : type1400 a0) := forall y0 : a1, forall y1 : a1 -> Prop, (@iterate a0 a1 x1 y1 (fun y2 : a1 => @COND a0 (y2 = y0) (x0 y2) (@neutral a0 x1))) = (@COND a0 (@IN a1 y0 y1) (x0 y0) (@neutral a0 x1)).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := @eq nat (@nsum a0 x0 (fun y0 : a0 => @COND nat (y0 = x1) x2 (NUMERAL 0))).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := fun y0 : a0 => (@iterate nat a0 Nat.add x0 (fun y1 : a0 => @COND nat (y1 = y0) x1 (@neutral nat Nat.add))) = (@COND nat (@IN a0 y0 x0) x1 (@neutral nat Nat.add)).
Definition term13 (a0 : Type') (x0 : a0) (x1 : nat) := fun y0 : a0 => @COND nat (y0 = x0) x1 (NUMERAL 0).
Definition term14 (a0 : Type') (x0 : a0) (x1 : nat) := fun y0 : a0 => @COND nat (y0 = x0) x1 (@neutral nat Nat.add).
Definition term50 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term38 (a0 : Type') (x0 : a0) (x1 : nat) := fun y0 : a0 => @COND nat (y0 = x0) ((fun y1 : a0 => x1) y0) (@neutral nat Nat.add).
Definition term46 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := @eq nat (@COND nat (@IN a0 x0 x1) x2 (@neutral nat Nat.add)).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1) (x2 : type1400 a0) := forall y0 : a1 -> Prop, (@iterate a0 a1 x2 y0 (fun y1 : a1 => @COND a0 (y1 = x1) (x0 y1) (@neutral a0 x2))) = (@COND a0 (@IN a1 x1 y0) (x0 x1) (@neutral a0 x2)).
Definition term22 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := fun y0 : a0 => (@nsum a0 x0 (fun y1 : a0 => @COND nat (y1 = y0) x1 (NUMERAL 0))) = (@COND nat (@IN a0 y0 x0) x1 (NUMERAL 0)).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1) (x2 : type1400 a0) (x3 : a1 -> Prop) := (fun y0 : a1 -> Prop => (@iterate a0 a1 x2 y0 (fun y1 : a1 => @COND a0 (y1 = x1) (x0 y1) (@neutral a0 x2))) = (@COND a0 (@IN a1 x1 y0) (x0 x1) (@neutral a0 x2))) x3.
Definition term3 (a0 : Type') (a1 : Type') (x0 : type1400 a0) (x1 : a1 -> a0) := (fun y0 : a1 -> a0 => forall y1 : a1, forall y2 : a1 -> Prop, (@iterate a0 a1 x0 y2 (fun y3 : a1 => @COND a0 (y3 = y1) (y0 y3) (@neutral a0 x0))) = (@COND a0 (@IN a1 y1 y2) (y0 y1) (@neutral a0 x0))) x1.
Definition term21 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := @COND nat (@IN a0 x0 x1) x2 (@neutral nat Nat.add).
Definition term12 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : nat) := @COND nat (x0 = x1) x2 (@neutral nat Nat.add).
Definition term36 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : a0) := @COND nat (x2 = x0) ((fun y0 : a0 => x1) x2).
Definition term2 (a0 : Type') (a1 : Type') (x0 : type1400 a0) := forall y0 : a1 -> a0, forall y1 : a1, forall y2 : a1 -> Prop, (@iterate a0 a1 x0 y2 (fun y3 : a1 => @COND a0 (y3 = y1) (y0 y3) (@neutral a0 x0))) = (@COND a0 (@IN a1 y1 y2) (y0 y1) (@neutral a0 x0)).
Definition term19 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := @COND nat (@IN a0 x0 x1) x2.
Definition term20 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := @COND nat (@IN a0 x0 x1) x2 (NUMERAL 0).
Definition term11 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : nat) := @COND nat (x0 = x1) x2 (NUMERAL 0).
Definition term29 (a0 : Type') (x0 : nat) := forall y0 : a0 -> Prop, forall y1 : a0, (@iterate nat a0 Nat.add y0 (fun y2 : a0 => @COND nat (y2 = y1) x0 (@neutral nat Nat.add))) = (@COND nat (@IN a0 y1 y0) x0 (@neutral nat Nat.add)).
Definition term28 (a0 : Type') (x0 : nat) := forall y0 : a0 -> Prop, forall y1 : a0, (@nsum a0 y0 (fun y2 : a0 => @COND nat (y2 = y1) x0 (NUMERAL 0))) = (@COND nat (@IN a0 y1 y0) x0 (NUMERAL 0)).
Definition term41 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @COND nat (@IN a0 x0 x1).
Definition term51 (a0 : Type') := forall y0 : a0 -> Prop, True.
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := @eq nat (@iterate nat a0 Nat.add x0 (fun y0 : a0 => @COND nat (y0 = x1) ((fun y1 : a0 => x2) y0) (@neutral nat Nat.add))).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : nat) := @eq nat (@iterate nat a0 Nat.add x0 (fun y0 : a0 => @COND nat (y0 = x1) x2 (@neutral nat Nat.add))).
