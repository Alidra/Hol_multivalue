Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term63 (a0 : Type') (x0 : a0 -> nat) (x1 : nat) (x2 : a0) (x3 : a0 -> Prop) := ((@IN a0 x2 x3) -> (Peano.le (x0 x2) ((fun y0 : a0 => x1) x2)) = True) -> ((@IN a0 x2 x3) -> Peano.le (x0 x2) ((fun y0 : a0 => x1) x2)) = ((@IN a0 x2 x3) -> True).
Definition term21 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (Nat.mul (@CARD a0 y1) y0) = (@nsum a0 y1 (fun y2 : a0 => y0))) x0.
Definition term5 (a0 : Type') (x0 : nat) := fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@nsum a0 y0 (fun y1 : a0 => x0)) = (Nat.mul (@CARD a0 y0) x0).
Definition term43 (a0 : Type') (x0 : nat) := fun y0 : a0 => x0.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := imp (@FINITE a0 x0).
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) x2.
Definition term75 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := ((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) x2)) -> True.
Definition term70 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term82 (a0 : Type') := fun y0 : a0 -> nat => True.
Definition term88 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> nat, forall y2 : nat, ((@FINITE a0 y0) /\ (forall y3 : a0, (@IN a0 y3 y0) -> Peano.le (y1 y3) y2)) -> Peano.le (@nsum a0 y0 y1) (Nat.mul (@CARD a0 y0) y2).
Definition term52 (a0 : Type') (x0 : a0 -> nat) (x1 : nat) (x2 : a0) (x3 : a0 -> Prop) (x4 : Prop) := ((@IN a0 x2 x3) -> (Peano.le (x0 x2) ((fun y0 : a0 => x1) x2)) = x4) -> ((@IN a0 x2 x3) -> Peano.le (x0 x2) ((fun y0 : a0 => x1) x2)) = ((@IN a0 x2 x3) -> x4).
Definition term55 (a0 : Type') (x0 : nat) (x1 : a0) := (fun y0 : a0 => (fun y1 : a0 => x0) y0) x1.
Definition term69 (a0 : Type') := forall y0 : a0, True.
Definition term13 (a0 : Type') (x0 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : a0 -> nat, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (forall y3 : a0, (@IN a0 y3 y2) -> Peano.le (y0 y3) (y1 y3))) -> Peano.le (@nsum a0 y2 y0) (@nsum a0 y2 y1)) x0.
Definition term17 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ (forall y1 : a0, (@IN a0 y1 y0) -> Peano.le (x0 y1) (x1 y1))) -> Peano.le (@nsum a0 y0 x0) (@nsum a0 y0 x1)) x2.
Definition term68 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) ((fun y1 : a0 => x2) y0).
Definition term65 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 x1) -> True.
Definition term90 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, x0.
Definition term85 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> nat, x0.
Definition term10 (a0 : Type') := fun y0 : nat => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (Nat.mul (@CARD a0 y1) y0) = (@nsum a0 y1 (fun y2 : a0 => y0)).
Definition term9 (a0 : Type') := fun y0 : nat => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@nsum a0 y1 (fun y2 : a0 => y0)) = (Nat.mul (@CARD a0 y1) y0).
Definition term8 (a0 : Type') (x0 : nat) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (Nat.mul (@CARD a0 y0) x0) = (@nsum a0 y0 (fun y1 : a0 => x0)).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) (x3 : Prop) := (((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) x2)) -> (Peano.le (@nsum a0 x0 x1) (Nat.mul (@CARD a0 x0) x2)) = x3) -> (((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) x2)) -> Peano.le (@nsum a0 x0 x1) (Nat.mul (@CARD a0 x0) x2)) = (((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) x2)) -> x3).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) (x3 : a0) (x4 : Prop) (x5 : Prop) := ((@IN a0 x3 x0) = x4) -> (x4 -> (Peano.le (x1 x3) ((fun y0 : a0 => x2) x3)) = x5) -> ((@IN a0 x3 x0) -> Peano.le (x1 x3) ((fun y0 : a0 => x2) x3)) = (x4 -> x5).
Definition term58 (a0 : Type') (x0 : nat) (x1 : a0) := @eq nat ((fun y0 : a0 => (fun y1 : a0 => x0) y0) x1).
Definition term64 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) (x3 : a0) := (@IN a0 x3 x0) -> Peano.le (x1 x3) ((fun y0 : a0 => x2) x3).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) -> (Nat.mul (@CARD a0 x0) x1) = (@nsum a0 x0 (fun y0 : a0 => x1)).
Definition term29 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : nat) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, (((@FINITE a0 x1) /\ (forall y2 : a0, (@IN a0 y2 x1) -> Peano.le (x0 y2) x2)) = y0) -> (y0 -> (Peano.le (@nsum a0 x1 x0) (Nat.mul (@CARD a0 x1) x2)) = y1) -> (((@FINITE a0 x1) /\ (forall y2 : a0, (@IN a0 y2 x1) -> Peano.le (x0 y2) x2)) -> Peano.le (@nsum a0 x1 x0) (Nat.mul (@CARD a0 x1) x2)) = (y0 -> y1)) x3.
Definition term42 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : nat) := ((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x0 y0) ((fun y1 : a0 => x2) y0))) -> (Peano.le (@nsum a0 x1 x0) (@nsum a0 x1 (fun y0 : a0 => x2))) = True.
Definition term51 (a0 : Type') (x0 : a0 -> nat) (x1 : nat) (x2 : a0) (x3 : a0 -> Prop) (x4 : Prop) := ((@IN a0 x2 x3) = (@IN a0 x2 x3)) -> ((@IN a0 x2 x3) -> (Peano.le (x0 x2) ((fun y0 : a0 => x1) x2)) = x4) -> ((@IN a0 x2 x3) -> Peano.le (x0 x2) ((fun y0 : a0 => x1) x2)) = ((@IN a0 x2 x3) -> x4).
Definition term20 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := Peano.le (@nsum a0 x1 x0) (@nsum a0 x1 x2).
Definition term60 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := Peano.le (x0 x1).
Definition term7 (a0 : Type') (x0 : nat) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@nsum a0 y0 (fun y1 : a0 => x0)) = (Nat.mul (@CARD a0 y0) x0).
Definition term15 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (forall y2 : a0, (@IN a0 y2 y1) -> Peano.le (x0 y2) (y0 y2))) -> Peano.le (@nsum a0 y1 x0) (@nsum a0 y1 y0)) x1.
Definition term81 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> nat => forall y1 : nat, ((@FINITE a0 x0) /\ (forall y2 : a0, (@IN a0 y2 x0) -> Peano.le (y0 y2) y1)) -> Peano.le (@nsum a0 x0 y0) (Nat.mul (@CARD a0 x0) y1).
Definition term18 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := ((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x0 y0) (x2 y0))) -> Peano.le (@nsum a0 x1 x0) (@nsum a0 x1 x2).
Definition term76 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) := fun y0 : nat => ((@FINITE a0 x1) /\ (forall y1 : a0, (@IN a0 y1 x1) -> Peano.le (x0 y1) y0)) -> Peano.le (@nsum a0 x1 x0) (Nat.mul (@CARD a0 x1) y0).
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : nat) := (@IN a0 x2 x0) -> (Peano.le (x1 x2) x3) = True.
Definition term44 (a0 : Type') (x0 : a0 -> Prop) := and (@FINITE a0 x0).
Definition term23 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term37 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : nat) := (@IN a0 x2 x0) -> Peano.le (x1 x2) x3.
Definition term6 (a0 : Type') (x0 : nat) := fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (Nat.mul (@CARD a0 y0) x0) = (@nsum a0 y0 (fun y1 : a0 => x0)).
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) (x3 : a0) := (fun y0 : a0 => (@IN a0 y0 x0) -> Peano.le (x1 y0) x2) x3.
Definition term53 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term59 (a0 : Type') (x0 : nat) (x1 : a0) := @eq nat ((fun y0 : a0 => x0) x1).
Definition term32 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : nat) (x3 : Prop) (x4 : Prop) := (((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x0 y0) x2)) = x3) -> (x3 -> (Peano.le (@nsum a0 x1 x0) (Nat.mul (@CARD a0 x1) x2)) = x4) -> (((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x0 y0) x2)) -> Peano.le (@nsum a0 x1 x0) (Nat.mul (@CARD a0 x1) x2)) = (x3 -> x4).
Definition term73 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := (((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) x2)) -> (Peano.le (@nsum a0 x0 x1) (Nat.mul (@CARD a0 x0) x2)) = True) -> (((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) x2)) -> Peano.le (@nsum a0 x0 x1) (Nat.mul (@CARD a0 x0) x2)) = (((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) x2)) -> True).
Definition term56 (a0 : Type') (x0 : nat) (x1 : a0) := (fun y0 : a0 => x0) x1.
Definition term12 (a0 : Type') := forall y0 : nat, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (Nat.mul (@CARD a0 y1) y0) = (@nsum a0 y1 (fun y2 : a0 => y0)).
Definition term11 (a0 : Type') := forall y0 : nat, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@nsum a0 y1 (fun y2 : a0 => y0)) = (Nat.mul (@CARD a0 y1) y0).
Definition term67 (a0 : Type') := fun y0 : a0 => True.
Definition term54 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term66 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := fun y0 : a0 => (@IN a0 y0 x0) -> Peano.le (x1 y0) ((fun y1 : a0 => x2) y0).
Definition term79 := forall y0 : nat, True.
Definition term77 := fun y0 : nat => True.
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) -> (@nsum a0 x0 (fun y0 : a0 => x1)) = (Nat.mul (@CARD a0 x0) x1).
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) (x3 : a0) (x4 : Prop) := forall y0 : Prop, ((@IN a0 x3 x0) = x4) -> (x4 -> (Peano.le (x1 x3) ((fun y1 : a0 => x2) x3)) = y0) -> ((@IN a0 x3 x0) -> Peano.le (x1 x3) ((fun y1 : a0 => x2) x3)) = (x4 -> y0).
Definition term30 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : nat) (x3 : Prop) := forall y0 : Prop, (((@FINITE a0 x1) /\ (forall y1 : a0, (@IN a0 y1 x1) -> Peano.le (x0 y1) x2)) = x3) -> (x3 -> (Peano.le (@nsum a0 x1 x0) (Nat.mul (@CARD a0 x1) x2)) = y0) -> (((@FINITE a0 x1) /\ (forall y1 : a0, (@IN a0 y1 x1) -> Peano.le (x0 y1) x2)) -> Peano.le (@nsum a0 x1 x0) (Nat.mul (@CARD a0 x1) x2)) = (x3 -> y0).
Definition term24 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term22 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (Nat.mul (@CARD a0 y0) x0) = (@nsum a0 y0 (fun y1 : a0 => x0))) x1.
Definition term87 (a0 : Type') := fun y0 : a0 -> Prop => True.
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := Peano.le (@nsum a0 x0 x1).
Definition term45 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) (x3 : a0) := forall y0 : Prop, forall y1 : Prop, ((@IN a0 x3 x0) = y0) -> (y0 -> (Peano.le (x1 x3) ((fun y2 : a0 => x2) x3)) = y1) -> ((@IN a0 x3 x0) -> Peano.le (x1 x3) ((fun y2 : a0 => x2) x3)) = (y0 -> y1).
Definition term26 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : nat) := forall y0 : Prop, forall y1 : Prop, (((@FINITE a0 x1) /\ (forall y2 : a0, (@IN a0 y2 x1) -> Peano.le (x0 y2) x2)) = y0) -> (y0 -> (Peano.le (@nsum a0 x1 x0) (Nat.mul (@CARD a0 x1) x2)) = y1) -> (((@FINITE a0 x1) /\ (forall y2 : a0, (@IN a0 y2 x1) -> Peano.le (x0 y2) x2)) -> Peano.le (@nsum a0 x1 x0) (Nat.mul (@CARD a0 x1) x2)) = (y0 -> y1).
Definition term25 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := Nat.mul (@CARD a0 x0) x1.
Definition term83 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> nat, forall y1 : nat, ((@FINITE a0 x0) /\ (forall y2 : a0, (@IN a0 y2 x0) -> Peano.le (y0 y2) y1)) -> Peano.le (@nsum a0 x0 y0) (Nat.mul (@CARD a0 x0) y1).
Definition term14 (a0 : Type') (x0 : a0 -> nat) := forall y0 : a0 -> nat, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (forall y2 : a0, (@IN a0 y2 y1) -> Peano.le (x0 y2) (y0 y2))) -> Peano.le (@nsum a0 y1 x0) (@nsum a0 y1 y0).
Definition term31 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : nat) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => (((@FINITE a0 x1) /\ (forall y1 : a0, (@IN a0 y1 x1) -> Peano.le (x0 y1) x2)) = x3) -> (x3 -> (Peano.le (@nsum a0 x1 x0) (Nat.mul (@CARD a0 x1) x2)) = y0) -> (((@FINITE a0 x1) /\ (forall y1 : a0, (@IN a0 y1 x1) -> Peano.le (x0 y1) x2)) -> Peano.le (@nsum a0 x1 x0) (Nat.mul (@CARD a0 x1) x2)) = (x3 -> y0)) x4.
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) (x3 : a0) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => ((@IN a0 x3 x0) = x4) -> (x4 -> (Peano.le (x1 x3) ((fun y1 : a0 => x2) x3)) = y0) -> ((@IN a0 x3 x0) -> Peano.le (x1 x3) ((fun y1 : a0 => x2) x3)) = (x4 -> y0)) x5.
Definition term40 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : nat) := Peano.le (@nsum a0 x1 x0) (@nsum a0 x1 (fun y0 : a0 => x2)).
Definition term78 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) := forall y0 : nat, ((@FINITE a0 x1) /\ (forall y1 : a0, (@IN a0 y1 x1) -> Peano.le (x0 y1) y0)) -> Peano.le (@nsum a0 x1 x0) (Nat.mul (@CARD a0 x1) y0).
Definition term57 (a0 : Type') (x0 : nat) := fun y0 : a0 => (fun y1 : a0 => x0) y0.
Definition term38 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) (x2 : nat) := Peano.le (x0 x1) x2.
Definition term71 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := (@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) ((fun y1 : a0 => x2) y0)).
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := (@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) x2).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := (@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) (x2 y0)).
Definition term46 (a0 : Type') (x0 : a0 -> nat) (x1 : nat) (x2 : a0) := Peano.le (x0 x2) ((fun y0 : a0 => x1) x2).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @nsum a0 x0 (fun y0 : a0 => x1).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) (x3 : Prop) := (((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) x2)) = ((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) x2))) -> (((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) x2)) -> (Peano.le (@nsum a0 x0 x1) (Nat.mul (@CARD a0 x0) x2)) = x3) -> (((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) x2)) -> Peano.le (@nsum a0 x0 x1) (Nat.mul (@CARD a0 x0) x2)) = (((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) x2)) -> x3).
Definition term62 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) (x3 : a0) := (@IN a0 x3 x0) -> (Peano.le (x1 x3) ((fun y0 : a0 => x2) x3)) = True.
Definition term80 (x0 : Prop) := forall y0 : nat, x0.
Definition term72 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : nat) := ((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x0 y0) x2)) -> (Peano.le (@nsum a0 x1 x0) (Nat.mul (@CARD a0 x1) x2)) = True.
Definition term41 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := ((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x0 y0) (x2 y0))) -> (Peano.le (@nsum a0 x1 x0) (@nsum a0 x1 x2)) = True.
Definition term74 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : nat) := ((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x0 y0) x2)) -> Peano.le (@nsum a0 x1 x0) (Nat.mul (@CARD a0 x1) x2).
Definition term86 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> nat, forall y2 : nat, ((@FINITE a0 y0) /\ (forall y3 : a0, (@IN a0 y3 y0) -> Peano.le (y1 y3) y2)) -> Peano.le (@nsum a0 y0 y1) (Nat.mul (@CARD a0 y0) y2).
Definition term28 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : nat) := Peano.le (@nsum a0 x1 x0) (Nat.mul (@CARD a0 x1) x2).
Definition term16 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (forall y1 : a0, (@IN a0 y1 y0) -> Peano.le (x0 y1) (x1 y1))) -> Peano.le (@nsum a0 y0 x0) (@nsum a0 y0 x1).
Definition term47 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) (x3 : a0) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@IN a0 x3 x0) = y0) -> (y0 -> (Peano.le (x1 x3) ((fun y2 : a0 => x2) x3)) = y1) -> ((@IN a0 x3 x0) -> Peano.le (x1 x3) ((fun y2 : a0 => x2) x3)) = (y0 -> y1)) x4.
Definition term89 (a0 : Type') := forall y0 : a0 -> Prop, True.
Definition term84 (a0 : Type') := forall y0 : a0 -> nat, True.
