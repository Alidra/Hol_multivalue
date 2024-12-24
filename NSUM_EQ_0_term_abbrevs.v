Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term43 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : Prop) := ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral nat Nat.add)) = (forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral nat Nat.add))) -> ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral nat Nat.add)) -> ((@iterate nat a0 Nat.add x0 x1) = (@neutral nat Nat.add)) = x2) -> ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral nat Nat.add)) -> (@iterate nat a0 Nat.add x0 x1) = (@neutral nat Nat.add)) = ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral nat Nat.add)) -> x2).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : type1400 a1) := (@monoidal a1 x2) -> (@iterate a1 a0 x2 x0 x1) = (@neutral a1 x2).
Definition term57 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) (x2 : a0 -> Prop) := ((@IN a0 x1 x2) -> ((x0 x1) = (@neutral nat Nat.add)) = True) -> ((@IN a0 x1 x2) -> (x0 x1) = (@neutral nat Nat.add)) = ((@IN a0 x1 x2) -> True).
Definition term10 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> x1 -> x2.
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := (@monoidal a1 x0) -> forall y0 : a0 -> a1, forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y1) -> (y0 y2) = (@neutral a1 x0)) -> (@iterate a1 a0 x0 y1 y0) = (@neutral a1 x0).
Definition term3 (a0 : Type') (a1 : Type') (x0 : type1400 a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y1) -> (y0 y2) = (@neutral a1 x0)) -> (@iterate a1 a0 x0 y1 y0) = (@neutral a1 x0)) x1.
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : type1400 a1) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (forall y1 : a0, (@IN a0 y1 y0) -> (x0 y1) = (@neutral a1 x1)) -> (@iterate a1 a0 x1 y0 x0) = (@neutral a1 x1)) x2.
Definition term61 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term70 (a0 : Type') := fun y0 : a0 -> nat => True.
Definition term53 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := ((@IN a0 x1 x2) = (@IN a0 x1 x2)) -> ((@IN a0 x1 x2) -> ((x0 x1) = (@neutral nat Nat.add)) = x3) -> ((@IN a0 x1 x2) -> (x0 x1) = (@neutral nat Nat.add)) = ((@IN a0 x1 x2) -> x3).
Definition term55 := @eq nat (@neutral nat Nat.add).
Definition term22 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := imp (forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral nat Nat.add)).
Definition term21 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := imp (forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (NUMERAL 0)).
Definition term60 (a0 : Type') := forall y0 : a0, True.
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : type1400 a1) := forall y0 : a0 -> Prop, (forall y1 : a0, (@IN a0 y1 y0) -> (x0 y1) = (@neutral a1 x1)) -> (@iterate a1 a0 x1 y0 x0) = (@neutral a1 x1).
Definition term58 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 x1) -> True.
Definition term72 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> nat, x0.
Definition term69 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term62 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := and (forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral nat Nat.add)).
Definition term66 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := (forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral nat Nat.add)) -> True.
Definition term27 (a0 : Type') (x0 : a0 -> nat) := fun y0 : a0 -> Prop => (forall y1 : a0, (@IN a0 y1 y0) -> (x0 y1) = (NUMERAL 0)) -> (@nsum a0 y0 x0) = (NUMERAL 0).
Definition term13 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := @eq nat (x0 x1).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@IN a0 x2 x0) = y0) -> (y0 -> ((x1 x2) = (@neutral nat Nat.add)) = y1) -> ((@IN a0 x2 x0) -> (x1 x2) = (@neutral nat Nat.add)) = (y0 -> y1)) x3.
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : type1400 a1) := forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral a1 x2).
Definition term47 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral nat Nat.add)) /\ (@monoidal nat Nat.add)) -> (@iterate nat a0 Nat.add x0 x1) = (@neutral nat Nat.add).
Definition term30 (a0 : Type') (x0 : a0 -> nat) := forall y0 : a0 -> Prop, (forall y1 : a0, (@IN a0 y1 y0) -> (x0 y1) = (@neutral nat Nat.add)) -> (@iterate nat a0 Nat.add y0 x0) = (@neutral nat Nat.add).
Definition term29 (a0 : Type') (x0 : a0 -> nat) := forall y0 : a0 -> Prop, (forall y1 : a0, (@IN a0 y1 y0) -> (x0 y1) = (NUMERAL 0)) -> (@nsum a0 y0 x0) = (NUMERAL 0).
Definition term56 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) := (@IN a0 x2 x0) -> ((x1 x2) = (@neutral nat Nat.add)) = True.
Definition term16 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) := (@IN a0 x2 x0) -> (x1 x2) = (@neutral nat Nat.add).
Definition term35 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term52 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : Prop) (x4 : Prop) := ((@IN a0 x2 x0) = x3) -> (x3 -> ((x1 x2) = (@neutral nat Nat.add)) = x4) -> ((@IN a0 x2 x0) -> (x1 x2) = (@neutral nat Nat.add)) = (x3 -> x4).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := (forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (NUMERAL 0)) -> (@nsum a0 x0 x1) = (NUMERAL 0).
Definition term59 (a0 : Type') := fun y0 : a0 => True.
Definition term41 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((forall y1 : a0, (@IN a0 y1 x0) -> (x1 y1) = (@neutral nat Nat.add)) = x2) -> (x2 -> ((@iterate nat a0 Nat.add x0 x1) = (@neutral nat Nat.add)) = y0) -> ((forall y1 : a0, (@IN a0 y1 x0) -> (x1 y1) = (@neutral nat Nat.add)) -> (@iterate nat a0 Nat.add x0 x1) = (@neutral nat Nat.add)) = (x2 -> y0)) x3.
Definition term64 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := (forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral nat Nat.add)) -> ((@iterate nat a0 Nat.add x0 x1) = (@neutral nat Nat.add)) = True.
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := fun y0 : a0 => (@IN a0 y0 x0) -> (x1 y0) = (@neutral nat Nat.add).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : Prop) := forall y0 : Prop, ((@IN a0 x2 x0) = x3) -> (x3 -> ((x1 x2) = (@neutral nat Nat.add)) = y0) -> ((@IN a0 x2 x0) -> (x1 x2) = (@neutral nat Nat.add)) = (x3 -> y0).
Definition term40 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : Prop) := forall y0 : Prop, ((forall y1 : a0, (@IN a0 y1 x0) -> (x1 y1) = (@neutral nat Nat.add)) = x2) -> (x2 -> ((@iterate nat a0 Nat.add x0 x1) = (@neutral nat Nat.add)) = y0) -> ((forall y1 : a0, (@IN a0 y1 x0) -> (x1 y1) = (@neutral nat Nat.add)) -> (@iterate nat a0 Nat.add x0 x1) = (@neutral nat Nat.add)) = (x2 -> y0).
Definition term36 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term45 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) := (fun y0 : a0 => (@IN a0 y0 x0) -> (x1 y0) = (@neutral nat Nat.add)) x2.
Definition term67 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term32 (a0 : Type') := fun y0 : a0 -> nat => forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y1) -> (y0 y2) = (@neutral nat Nat.add)) -> (@iterate nat a0 Nat.add y1 y0) = (@neutral nat Nat.add).
Definition term31 (a0 : Type') := fun y0 : a0 -> nat => forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y1) -> (y0 y2) = (NUMERAL 0)) -> (@nsum a0 y1 y0) = (NUMERAL 0).
Definition term11 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) -> x2.
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) := forall y0 : Prop, forall y1 : Prop, ((@IN a0 x2 x0) = y0) -> (y0 -> ((x1 x2) = (@neutral nat Nat.add)) = y1) -> ((@IN a0 x2 x0) -> (x1 x2) = (@neutral nat Nat.add)) = (y0 -> y1).
Definition term38 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := forall y0 : Prop, forall y1 : Prop, ((forall y2 : a0, (@IN a0 y2 x0) -> (x1 y2) = (@neutral nat Nat.add)) = y0) -> (y0 -> ((@iterate nat a0 Nat.add x0 x1) = (@neutral nat Nat.add)) = y1) -> ((forall y2 : a0, (@IN a0 y2 x0) -> (x1 y2) = (@neutral nat Nat.add)) -> (@iterate nat a0 Nat.add x0 x1) = (@neutral nat Nat.add)) = (y0 -> y1).
Definition term37 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term14 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term54 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := ((@IN a0 x1 x2) -> ((x0 x1) = (@neutral nat Nat.add)) = x3) -> ((@IN a0 x1 x2) -> (x0 x1) = (@neutral nat Nat.add)) = ((@IN a0 x1 x2) -> x3).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : type1400 a1) := (forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral a1 x2)) -> (@monoidal a1 x2) -> (@iterate a1 a0 x2 x0 x1) = (@neutral a1 x2).
Definition term34 (a0 : Type') := forall y0 : a0 -> nat, forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y1) -> (y0 y2) = (@neutral nat Nat.add)) -> (@iterate nat a0 Nat.add y1 y0) = (@neutral nat Nat.add).
Definition term33 (a0 : Type') := forall y0 : a0 -> nat, forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y1) -> (y0 y2) = (NUMERAL 0)) -> (@nsum a0 y1 y0) = (NUMERAL 0).
Definition term2 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := forall y0 : a0 -> a1, forall y1 : a0 -> Prop, (forall y2 : a0, (@IN a0 y2 y1) -> (y0 y2) = (@neutral a1 x0)) -> (@iterate a1 a0 x0 y1 y0) = (@neutral a1 x0).
Definition term51 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((@IN a0 x2 x0) = x3) -> (x3 -> ((x1 x2) = (@neutral nat Nat.add)) = y0) -> ((@IN a0 x2 x0) -> (x1 x2) = (@neutral nat Nat.add)) = (x3 -> y0)) x4.
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral nat Nat.add).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (NUMERAL 0).
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := (forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral nat Nat.add)) /\ (@monoidal nat Nat.add).
Definition term46 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : type1606) := ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral nat x2)) /\ (@monoidal nat x2)) -> (@iterate nat a0 x2 x0 x1) = (@neutral nat x2).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : type1400 a1) := ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral a1 x2)) /\ (@monoidal a1 x2)) -> (@iterate a1 a0 x2 x0 x1) = (@neutral a1 x2).
Definition term44 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : Prop) := ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral nat Nat.add)) -> ((@iterate nat a0 Nat.add x0 x1) = (@neutral nat Nat.add)) = x2) -> ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral nat Nat.add)) -> (@iterate nat a0 Nat.add x0 x1) = (@neutral nat Nat.add)) = ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral nat Nat.add)) -> x2).
Definition term15 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) := (@IN a0 x2 x0) -> (x1 x2) = (NUMERAL 0).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := @eq nat (@nsum a0 x0 x1).
Definition term28 (a0 : Type') (x0 : a0 -> nat) := fun y0 : a0 -> Prop => (forall y1 : a0, (@IN a0 y1 y0) -> (x0 y1) = (@neutral nat Nat.add)) -> (@iterate nat a0 Nat.add y0 x0) = (@neutral nat Nat.add).
Definition term65 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral nat Nat.add)) -> ((@iterate nat a0 Nat.add x0 x1) = (@neutral nat Nat.add)) = True) -> ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral nat Nat.add)) -> (@iterate nat a0 Nat.add x0 x1) = (@neutral nat Nat.add)) = ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral nat Nat.add)) -> True).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := @eq nat (@iterate nat a0 Nat.add x0 x1).
Definition term0 (a0 : Type') (a1 : Type') (x0 : type1400 a1) := (fun y0 : type1400 a1 => (@monoidal a1 y0) -> forall y1 : a0 -> a1, forall y2 : a0 -> Prop, (forall y3 : a0, (@IN a0 y3 y2) -> (y1 y3) = (@neutral a1 y0)) -> (@iterate a1 a0 y0 y2 y1) = (@neutral a1 y0)) x0.
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : type1400 a1) := (forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral a1 x2)) -> (@iterate a1 a0 x2 x0 x1) = (@neutral a1 x2).
Definition term17 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := fun y0 : a0 => (@IN a0 y0 x0) -> (x1 y0) = (NUMERAL 0).
Definition term26 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := (forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral nat Nat.add)) -> (@iterate nat a0 Nat.add x0 x1) = (@neutral nat Nat.add).
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((forall y2 : a0, (@IN a0 y2 x0) -> (x1 y2) = (@neutral nat Nat.add)) = y0) -> (y0 -> ((@iterate nat a0 Nat.add x0 x1) = (@neutral nat Nat.add)) = y1) -> ((forall y2 : a0, (@IN a0 y2 x0) -> (x1 y2) = (@neutral nat Nat.add)) -> (@iterate nat a0 Nat.add x0 x1) = (@neutral nat Nat.add)) = (y0 -> y1)) x2.
Definition term42 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : Prop) (x3 : Prop) := ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral nat Nat.add)) = x2) -> (x2 -> ((@iterate nat a0 Nat.add x0 x1) = (@neutral nat Nat.add)) = x3) -> ((forall y0 : a0, (@IN a0 y0 x0) -> (x1 y0) = (@neutral nat Nat.add)) -> (@iterate nat a0 Nat.add x0 x1) = (@neutral nat Nat.add)) = (x2 -> x3).
Definition term71 (a0 : Type') := forall y0 : a0 -> nat, True.
Definition term68 (a0 : Type') := forall y0 : a0 -> Prop, True.
