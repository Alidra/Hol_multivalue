Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term13 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> x1 -> x2.
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := (@monoidal a1 x0) -> forall y0 : a0 -> a1, forall y1 : a0 -> a1, forall y2 : a0 -> Prop, (@FINITE a0 y2) -> (@iterate a1 a0 x0 y2 (fun y3 : a0 => x0 (y0 y3) (y1 y3))) = (x0 (@iterate a1 a0 x0 y2 y0) (@iterate a1 a0 x0 y2 y1)).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : type1400 a1) (x2 : a0 -> Prop) (x3 : a0 -> a1) := (@FINITE a0 x2) -> (@monoidal a1 x1) -> (@iterate a1 a0 x1 x2 (fun y0 : a0 => x1 (x0 y0) (x3 y0))) = (x1 (@iterate a1 a0 x1 x2 x0) (@iterate a1 a0 x1 x2 x3)).
Definition term47 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term50 (a0 : Type') := fun y0 : a0 -> nat => True.
Definition term55 (a0 : Type') := forall y0 : a0 -> nat, forall y1 : a0 -> nat, forall y2 : a0 -> Prop, (@FINITE a0 y2) -> (@nsum a0 y2 (fun y3 : a0 => Nat.add (y0 y3) (y1 y3))) = (Nat.add (@nsum a0 y2 y0) (@nsum a0 y2 y1)).
Definition term2 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := forall y0 : a0 -> a1, forall y1 : a0 -> a1, forall y2 : a0 -> Prop, (@FINITE a0 y2) -> (@iterate a1 a0 x0 y2 (fun y3 : a0 => x0 (y0 y3) (y1 y3))) = (x0 (@iterate a1 a0 x0 y2 y0) (@iterate a1 a0 x0 y2 y1)).
Definition term39 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := (@FINITE a0 x1) -> ((@nsum a0 x1 (fun y0 : a0 => Nat.add (x0 y0) (x2 y0))) = (Nat.add (@nsum a0 x1 x0) (@nsum a0 x1 x2))) = True.
Definition term37 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := Nat.add (@nsum a0 x0 x1).
Definition term21 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := Nat.add (@nsum a0 x1 x0) (@nsum a0 x1 x2).
Definition term53 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> nat, x0.
Definition term48 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term30 (a0 : Type') (x0 : a0 -> nat) (x1 : type1606) (x2 : a0 -> Prop) (x3 : a0 -> nat) := ((@FINITE a0 x2) /\ (@monoidal nat x1)) -> (@iterate nat a0 x1 x2 (fun y0 : a0 => x1 (x0 y0) (x3 y0))) = (x1 (@iterate nat a0 x1 x2 x0) (@iterate nat a0 x1 x2 x3)).
Definition term15 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : type1400 a1) (x2 : a0 -> Prop) (x3 : a0 -> a1) := ((@FINITE a0 x2) /\ (@monoidal a1 x1)) -> (@iterate a1 a0 x1 x2 (fun y0 : a0 => x1 (x0 y0) (x3 y0))) = (x1 (@iterate a1 a0 x1 x2 x0) (@iterate a1 a0 x1 x2 x3)).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) /\ (@monoidal nat Nat.add).
Definition term22 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@FINITE a0 x1) = y0) -> (y0 -> ((@nsum a0 x1 (fun y2 : a0 => Nat.add (x0 y2) (x2 y2))) = (Nat.add (@nsum a0 x1 x0) (@nsum a0 x1 x2))) = y1) -> ((@FINITE a0 x1) -> (@nsum a0 x1 (fun y2 : a0 => Nat.add (x0 y2) (x2 y2))) = (Nat.add (@nsum a0 x1 x0) (@nsum a0 x1 x2))) = (y0 -> y1)) x3.
Definition term28 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) := fun y0 : a0 => Nat.add (x0 y0) (x1 y0).
Definition term40 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) (x2 : a0 -> Prop) := ((@FINITE a0 x2) -> ((@nsum a0 x2 (fun y0 : a0 => Nat.add (x0 y0) (x1 y0))) = (Nat.add (@nsum a0 x2 x0) (@nsum a0 x2 x1))) = True) -> ((@FINITE a0 x2) -> (@nsum a0 x2 (fun y0 : a0 => Nat.add (x0 y0) (x1 y0))) = (Nat.add (@nsum a0 x2 x0) (@nsum a0 x2 x1))) = ((@FINITE a0 x2) -> True).
Definition term25 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) (x3 : Prop) (x4 : Prop) := ((@FINITE a0 x1) = x3) -> (x3 -> ((@nsum a0 x1 (fun y0 : a0 => Nat.add (x0 y0) (x2 y0))) = (Nat.add (@nsum a0 x1 x0) (@nsum a0 x1 x2))) = x4) -> ((@FINITE a0 x1) -> (@nsum a0 x1 (fun y0 : a0 => Nat.add (x0 y0) (x2 y0))) = (Nat.add (@nsum a0 x1 x0) (@nsum a0 x1 x2))) = (x3 -> x4).
Definition term26 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) (x2 : a0 -> Prop) (x3 : Prop) := ((@FINITE a0 x2) = (@FINITE a0 x2)) -> ((@FINITE a0 x2) -> ((@nsum a0 x2 (fun y0 : a0 => Nat.add (x0 y0) (x1 y0))) = (Nat.add (@nsum a0 x2 x0) (@nsum a0 x2 x1))) = x3) -> ((@FINITE a0 x2) -> (@nsum a0 x2 (fun y0 : a0 => Nat.add (x0 y0) (x1 y0))) = (Nat.add (@nsum a0 x2 x0) (@nsum a0 x2 x1))) = ((@FINITE a0 x2) -> x3).
Definition term32 (a0 : Type') (x0 : a0 -> Prop) := and (@FINITE a0 x0).
Definition term34 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := Nat.add (@iterate nat a0 Nat.add x1 x0) (@iterate nat a0 Nat.add x1 x2).
Definition term16 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term27 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) (x2 : a0 -> Prop) (x3 : Prop) := ((@FINITE a0 x2) -> ((@nsum a0 x2 (fun y0 : a0 => Nat.add (x0 y0) (x1 y0))) = (Nat.add (@nsum a0 x2 x0) (@nsum a0 x2 x1))) = x3) -> ((@FINITE a0 x2) -> (@nsum a0 x2 (fun y0 : a0 => Nat.add (x0 y0) (x1 y0))) = (Nat.add (@nsum a0 x2 x0) (@nsum a0 x2 x1))) = ((@FINITE a0 x2) -> x3).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : type1400 a1) (x2 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@iterate a1 a0 x1 y1 (fun y2 : a0 => x1 (x0 y2) (y0 y2))) = (x1 (@iterate a1 a0 x1 y1 x0) (@iterate a1 a0 x1 y1 y0))) x2.
Definition term31 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := ((@FINITE a0 x1) /\ (@monoidal nat Nat.add)) -> (@iterate nat a0 Nat.add x1 (fun y0 : a0 => Nat.add (x0 y0) (x2 y0))) = (Nat.add (@iterate nat a0 Nat.add x1 x0) (@iterate nat a0 Nat.add x1 x2)).
Definition term45 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@nsum a0 y0 (fun y1 : a0 => Nat.add (x0 y1) (x1 y1))) = (Nat.add (@nsum a0 y0 x0) (@nsum a0 y0 x1)).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : type1400 a1) (x2 : a0 -> a1) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@iterate a1 a0 x1 y0 (fun y1 : a0 => x1 (x0 y1) (x2 y1))) = (x1 (@iterate a1 a0 x1 y0 x0) (@iterate a1 a0 x1 y0 x2)).
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := @eq nat (@nsum a0 x0 (fun y0 : a0 => Nat.add (x1 y0) (x2 y0))).
Definition term23 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) (x3 : Prop) := forall y0 : Prop, ((@FINITE a0 x1) = x3) -> (x3 -> ((@nsum a0 x1 (fun y1 : a0 => Nat.add (x0 y1) (x2 y1))) = (Nat.add (@nsum a0 x1 x0) (@nsum a0 x1 x2))) = y0) -> ((@FINITE a0 x1) -> (@nsum a0 x1 (fun y1 : a0 => Nat.add (x0 y1) (x2 y1))) = (Nat.add (@nsum a0 x1 x0) (@nsum a0 x1 x2))) = (x3 -> y0).
Definition term17 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term44 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term49 (a0 : Type') (x0 : a0 -> nat) := fun y0 : a0 -> nat => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@nsum a0 y1 (fun y2 : a0 => Nat.add (x0 y2) (y0 y2))) = (Nat.add (@nsum a0 y1 x0) (@nsum a0 y1 y0)).
Definition term14 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) -> x2.
Definition term19 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := forall y0 : Prop, forall y1 : Prop, ((@FINITE a0 x1) = y0) -> (y0 -> ((@nsum a0 x1 (fun y2 : a0 => Nat.add (x0 y2) (x2 y2))) = (Nat.add (@nsum a0 x1 x0) (@nsum a0 x1 x2))) = y1) -> ((@FINITE a0 x1) -> (@nsum a0 x1 (fun y2 : a0 => Nat.add (x0 y2) (x2 y2))) = (Nat.add (@nsum a0 x1 x0) (@nsum a0 x1 x2))) = (y0 -> y1).
Definition term18 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term3 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> a1, forall y2 : a0 -> Prop, (@FINITE a0 y2) -> (@iterate a1 a0 x0 y2 (fun y3 : a0 => x0 (y0 y3) (y1 y3))) = (x0 (@iterate a1 a0 x0 y2 y0) (@iterate a1 a0 x0 y2 y1))) x1.
Definition term51 (a0 : Type') (x0 : a0 -> nat) := forall y0 : a0 -> nat, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@nsum a0 y1 (fun y2 : a0 => Nat.add (x0 y2) (y0 y2))) = (Nat.add (@nsum a0 y1 x0) (@nsum a0 y1 y0)).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : type1400 a1) := forall y0 : a0 -> a1, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@iterate a1 a0 x1 y1 (fun y2 : a0 => x1 (x0 y2) (y0 y2))) = (x1 (@iterate a1 a0 x1 y1 x0) (@iterate a1 a0 x1 y1 y0)).
Definition term24 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((@FINITE a0 x1) = x3) -> (x3 -> ((@nsum a0 x1 (fun y1 : a0 => Nat.add (x0 y1) (x2 y1))) = (Nat.add (@nsum a0 x1 x0) (@nsum a0 x1 x2))) = y0) -> ((@FINITE a0 x1) -> (@nsum a0 x1 (fun y1 : a0 => Nat.add (x0 y1) (x2 y1))) = (Nat.add (@nsum a0 x1 x0) (@nsum a0 x1 x2))) = (x3 -> y0)) x4.
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : type1400 a1) (x2 : a0 -> Prop) (x3 : a0 -> a1) := (@monoidal a1 x1) -> (@iterate a1 a0 x1 x2 (fun y0 : a0 => x1 (x0 y0) (x3 y0))) = (x1 (@iterate a1 a0 x1 x2 x0) (@iterate a1 a0 x1 x2 x3)).
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : type1400 a1) (x2 : a0 -> Prop) (x3 : a0 -> a1) := x1 (@iterate a1 a0 x1 x2 x0) (@iterate a1 a0 x1 x2 x3).
Definition term29 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := @iterate nat a0 Nat.add x0 (fun y0 : a0 => Nat.add (x1 y0) (x2 y0)).
Definition term0 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := (fun y0 : type1400 a1 => (@monoidal a1 y0) -> forall y1 : a0 -> a1, forall y2 : a0 -> a1, forall y3 : a0 -> Prop, (@FINITE a0 y3) -> (@iterate a1 a0 y0 y3 (fun y4 : a0 => y0 (y1 y4) (y2 y4))) = (y0 (@iterate a1 a0 y0 y3 y1) (@iterate a1 a0 y0 y3 y2))) x0.
Definition term38 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := Nat.add (@iterate nat a0 Nat.add x0 x1).
Definition term43 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) := fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@nsum a0 y0 (fun y1 : a0 => Nat.add (x0 y1) (x1 y1))) = (Nat.add (@nsum a0 y0 x0) (@nsum a0 y0 x1)).
Definition term54 (a0 : Type') := fun y0 : a0 -> nat => forall y1 : a0 -> nat, forall y2 : a0 -> Prop, (@FINITE a0 y2) -> (@nsum a0 y2 (fun y3 : a0 => Nat.add (y0 y3) (y1 y3))) = (Nat.add (@nsum a0 y2 y0) (@nsum a0 y2 y1)).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : type1400 a1) (x2 : a0 -> a1) (x3 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@iterate a1 a0 x1 y0 (fun y1 : a0 => x1 (x0 y1) (x2 y1))) = (x1 (@iterate a1 a0 x1 y0 x0) (@iterate a1 a0 x1 y0 x2))) x3.
Definition term42 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> True.
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1400 a1) (x2 : a0 -> a1) (x3 : a0 -> a1) := @iterate a1 a0 x1 x0 (fun y0 : a0 => x1 (x2 y0) (x3 y0)).
Definition term36 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := @eq nat (Nat.add (@iterate nat a0 Nat.add x1 x0) (@iterate nat a0 Nat.add x1 x2)).
Definition term41 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := (@FINITE a0 x1) -> (@nsum a0 x1 (fun y0 : a0 => Nat.add (x0 y0) (x2 y0))) = (Nat.add (@nsum a0 x1 x0) (@nsum a0 x1 x2)).
Definition term52 (a0 : Type') := forall y0 : a0 -> nat, True.
Definition term46 (a0 : Type') := forall y0 : a0 -> Prop, True.
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : type1400 a1) (x2 : a0 -> Prop) (x3 : a0 -> a1) := (@FINITE a0 x2) -> (@iterate a1 a0 x1 x2 (fun y0 : a0 => x1 (x0 y0) (x3 y0))) = (x1 (@iterate a1 a0 x1 x2 x0) (@iterate a1 a0 x1 x2 x3)).
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := @nsum a0 x0 (fun y0 : a0 => Nat.add (x1 y0) (x2 y0)).