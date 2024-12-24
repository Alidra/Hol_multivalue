Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term105 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (@SUBSET a0 (@INSERT a0 y1 (@EMPTY a0)) y0) = (@IN a0 y1 y0)) x0.
Definition term20 (a0 : Type') (x0 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : a0, (y0 y1) = (@nsum a0 (@INSERT a0 y1 (@EMPTY a0)) y0)) x0.
Definition term104 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) := ((@FINITE a0 x1) /\ (@SUBSET a0 (@INSERT a0 x0 (@EMPTY a0)) x1)) -> Peano.le (@nsum a0 (@INSERT a0 x0 (@EMPTY a0)) x2) (@nsum a0 x1 x2).
Definition term46 (a0 : Type') (x0 : a0 -> nat) := fun y0 : nat => forall y1 : a0 -> Prop, (Nat.mul y0 (@nsum a0 y1 x0)) = (@nsum a0 y1 (fun y2 : a0 => Nat.mul y0 (x0 y2))).
Definition term82 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) (x3 : a0) := (fun y0 : a0 => (fun y1 : a0 => Nat.mul (@nsum a0 x0 x1) (x2 y1)) y0) x3.
Definition term83 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) (x3 : a0) := (fun y0 : a0 => Nat.mul (@nsum a0 x0 x1) (x2 y0)) x3.
Definition term79 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) (x2 : a0) := @eq nat ((fun y0 : a0 => Nat.mul (x0 y0) (x1 y0)) x2).
Definition term64 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y0 y2) (Nat.mul y1 y2)) = ((Peano.le y0 y1) \/ (y2 = (NUMERAL 0)))) x0.
Definition term40 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := Nat.mul x0 (@nsum a0 x1 x2).
Definition term55 (a0 : Type') (x0 : nat) (x1 : a0 -> nat) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (Nat.mul x0 (@nsum a0 y0 x1)) = (@nsum a0 y0 (fun y1 : a0 => Nat.mul x0 (x1 y1)))) x2.
Definition term113 (a0 : Type') := forall y0 : a0 -> nat, forall y1 : a0 -> nat, forall y2 : a0 -> Prop, (@FINITE a0 y2) -> Peano.le (@nsum a0 y2 (fun y3 : a0 => Nat.mul (y0 y3) (y1 y3))) (Nat.mul (@nsum a0 y2 y0) (@nsum a0 y2 y1)).
Definition term52 (a0 : Type') := forall y0 : a0 -> nat, forall y1 : nat, forall y2 : a0 -> Prop, (Nat.mul y1 (@nsum a0 y2 y0)) = (@nsum a0 y2 (fun y3 : a0 => Nat.mul y1 (y0 y3))).
Definition term51 (a0 : Type') := forall y0 : a0 -> nat, forall y1 : nat, forall y2 : a0 -> Prop, (@nsum a0 y2 (fun y3 : a0 => Nat.mul y1 (y0 y3))) = (Nat.mul y1 (@nsum a0 y2 y0)).
Definition term34 (a0 : Type') := forall y0 : a0 -> nat, forall y1 : a0 -> Prop, forall y2 : a0 -> nat, ((@FINITE a0 y1) /\ (forall y3 : a0, (@IN a0 y3 y1) -> Peano.le (y0 y3) (y2 y3))) -> Peano.le (@nsum a0 y1 y0) (@nsum a0 y1 y2).
Definition term22 (a0 : Type') := forall y0 : a0 -> nat, forall y1 : a0 -> nat, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (forall y3 : a0, (@IN a0 y3 y2) -> Peano.le (y0 y3) (y1 y3))) -> Peano.le (@nsum a0 y2 y0) (@nsum a0 y2 y1).
Definition term0 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> nat, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> Peano.le (@nsum a0 y0 y2) (@nsum a0 y1 y2).
Definition term62 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) := fun y0 : a0 => Nat.mul (x0 y0) (x1 y0).
Definition term88 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) (x3 : a0) := Peano.le ((fun y0 : a0 => Nat.mul (x1 y0) (x2 y0)) x3) ((fun y0 : a0 => Nat.mul (@nsum a0 x0 x1) (x2 y0)) x3).
Definition term74 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) (x2 : a0) := (fun y0 : a0 => (fun y1 : a0 => Nat.mul (x0 y1) (x1 y1)) y0) x2.
Definition term99 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := True /\ (forall y0 : a0, (@IN a0 y0 x0) -> (Peano.le (x1 y0) (@nsum a0 x0 x1)) \/ ((x2 y0) = (NUMERAL 0))).
Definition term69 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term53 (a0 : Type') (x0 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : nat, forall y2 : a0 -> Prop, (Nat.mul y1 (@nsum a0 y2 y0)) = (@nsum a0 y2 (fun y3 : a0 => Nat.mul y1 (y0 y3)))) x0.
Definition term36 (a0 : Type') (x0 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : a0 -> Prop, forall y2 : a0 -> nat, ((@FINITE a0 y1) /\ (forall y3 : a0, (@IN a0 y3 y1) -> Peano.le (y0 y3) (y2 y3))) -> Peano.le (@nsum a0 y1 y0) (@nsum a0 y1 y2)) x0.
Definition term23 (a0 : Type') (x0 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : a0 -> nat, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (forall y3 : a0, (@IN a0 y3 y2) -> Peano.le (y0 y3) (y1 y3))) -> Peano.le (@nsum a0 y2 y0) (@nsum a0 y2 y1)) x0.
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0 -> nat, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> Peano.le (@nsum a0 y0 y2) (@nsum a0 y1 y2)) x0.
Definition term92 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) (x3 : a0) := (@IN a0 x3 x0) -> Peano.le ((fun y0 : a0 => Nat.mul (x1 y0) (x2 y0)) x3) ((fun y0 : a0 => Nat.mul (@nsum a0 x0 x1) (x2 y0)) x3).
Definition term38 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := (fun y0 : a0 -> nat => ((@FINITE a0 x1) /\ (forall y1 : a0, (@IN a0 y1 x1) -> Peano.le (x0 y1) (y0 y1))) -> Peano.le (@nsum a0 x1 x0) (@nsum a0 x1 y0)) x2.
Definition term27 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ (forall y1 : a0, (@IN a0 y1 y0) -> Peano.le (x0 y1) (x1 y1))) -> Peano.le (@nsum a0 y0 x0) (@nsum a0 y0 x1)) x2.
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> nat) := (fun y0 : a0 -> nat => ((@FINITE a0 x1) /\ (@SUBSET a0 x0 x1)) -> Peano.le (@nsum a0 x0 y0) (@nsum a0 x1 y0)) x2.
Definition term97 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := forall y0 : a0, (@IN a0 y0 x0) -> (Peano.le (x1 y0) (@nsum a0 x0 x1)) \/ ((x2 y0) = (NUMERAL 0)).
Definition term96 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := forall y0 : a0, (@IN a0 y0 x0) -> Peano.le ((fun y1 : a0 => Nat.mul (x1 y1) (x2 y1)) y0) ((fun y1 : a0 => Nat.mul (@nsum a0 x0 x1) (x2 y1)) y0).
Definition term68 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.mul x0 y0) (Nat.mul x1 y0)) = ((Peano.le x0 x1) \/ (y0 = (NUMERAL 0)))) x2.
Definition term95 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := fun y0 : a0 => (@IN a0 y0 x0) -> (Peano.le (x1 y0) (@nsum a0 x0 x1)) \/ ((x2 y0) = (NUMERAL 0)).
Definition term35 (a0 : Type') := (forall y0 : a0 -> nat, forall y1 : a0 -> nat, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (forall y3 : a0, (@IN a0 y3 y2) -> Peano.le (y0 y3) (y1 y3))) -> Peano.le (@nsum a0 y2 y0) (@nsum a0 y2 y1)) -> forall y0 : a0 -> nat, forall y1 : a0 -> Prop, forall y2 : a0 -> nat, ((@FINITE a0 y1) /\ (forall y3 : a0, (@IN a0 y3 y1) -> Peano.le (y0 y3) (y2 y3))) -> Peano.le (@nsum a0 y1 y0) (@nsum a0 y1 y2).
Definition term10 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> nat, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> Peano.le (@nsum a0 y0 y2) (@nsum a0 y1 y2)) -> forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> nat, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> Peano.le (@nsum a0 y0 y2) (@nsum a0 y1 y2).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> nat) := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> nat, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> Peano.le (@nsum a0 y0 y2) (@nsum a0 y1 y2)) -> Peano.le (@nsum a0 x0 x2) (@nsum a0 x1 x2).
Definition term90 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) (x3 : a0) := (Peano.le (x1 x3) (@nsum a0 x0 x1)) \/ ((x2 x3) = (NUMERAL 0)).
Definition term54 (a0 : Type') (x0 : a0 -> nat) (x1 : nat) := (fun y0 : nat => forall y1 : a0 -> Prop, (Nat.mul y0 (@nsum a0 y1 x0)) = (@nsum a0 y1 (fun y2 : a0 => Nat.mul y0 (x0 y2)))) x1.
Definition term50 (a0 : Type') := fun y0 : a0 -> nat => forall y1 : nat, forall y2 : a0 -> Prop, (Nat.mul y1 (@nsum a0 y2 y0)) = (@nsum a0 y2 (fun y3 : a0 => Nat.mul y1 (y0 y3))).
Definition term49 (a0 : Type') := fun y0 : a0 -> nat => forall y1 : nat, forall y2 : a0 -> Prop, (@nsum a0 y2 (fun y3 : a0 => Nat.mul y1 (y0 y3))) = (Nat.mul y1 (@nsum a0 y2 y0)).
Definition term109 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@FINITE a0 x1) /\ (@SUBSET a0 (@INSERT a0 x0 (@EMPTY a0)) x1).
Definition term78 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) (x2 : a0) := @eq nat ((fun y0 : a0 => (fun y1 : a0 => Nat.mul (x0 y1) (x1 y1)) y0) x2).
Definition term110 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := (@FINITE a0 x1) -> Peano.le (@nsum a0 x1 (fun y0 : a0 => Nat.mul (x0 y0) (x2 y0))) (Nat.mul (@nsum a0 x1 x0) (@nsum a0 x1 x2)).
Definition term56 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := Nat.mul (@nsum a0 x1 x0) (@nsum a0 x1 x2).
Definition term107 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (@SUBSET a0 (@INSERT a0 y0 (@EMPTY a0)) x0) = (@IN a0 y0 x0)) x1.
Definition term60 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := Peano.le (@nsum a0 x0 (fun y0 : a0 => Nat.mul (x1 y0) (x2 y0))) (@nsum a0 x0 (fun y0 : a0 => Nat.mul (@nsum a0 x0 x1) (x2 y0))).
Definition term30 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := Peano.le (@nsum a0 x1 x0) (@nsum a0 x1 x2).
Definition term86 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) (x3 : a0) := @eq nat ((fun y0 : a0 => (fun y1 : a0 => Nat.mul (@nsum a0 x0 x1) (x2 y1)) y0) x3).
Definition term85 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := fun y0 : a0 => (fun y1 : a0 => Nat.mul (@nsum a0 x0 x1) (x2 y1)) y0.
Definition term102 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) := Peano.le (x2 x0) (@nsum a0 x1 x2).
Definition term100 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := Peano.le (x0 x1).
Definition term67 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x1 y0)) = ((Peano.le x0 x1) \/ (y0 = (NUMERAL 0))).
Definition term66 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul x0 y1) (Nat.mul y0 y1)) = ((Peano.le x0 y0) \/ (y1 = (NUMERAL 0)))) x1.
Definition term37 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> nat, ((@FINITE a0 y0) /\ (forall y2 : a0, (@IN a0 y2 y0) -> Peano.le (x0 y2) (y1 y2))) -> Peano.le (@nsum a0 y0 x0) (@nsum a0 y0 y1)) x1.
Definition term25 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (forall y2 : a0, (@IN a0 y2 y1) -> Peano.le (x0 y2) (y0 y2))) -> Peano.le (@nsum a0 y1 x0) (@nsum a0 y1 y0)) x1.
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> nat, ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> Peano.le (@nsum a0 x0 y1) (@nsum a0 y0 y1)) x1.
Definition term16 (a0 : Type') := fun y0 : a0 -> nat => forall y1 : a0, (@nsum a0 (@INSERT a0 y1 (@EMPTY a0)) y0) = (y0 y1).
Definition term28 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := ((@FINITE a0 x1) /\ (forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x0 y0) (x2 y0))) -> Peano.le (@nsum a0 x1 x0) (@nsum a0 x1 x2).
Definition term15 (a0 : Type') (x0 : a0 -> nat) := forall y0 : a0, (x0 y0) = (@nsum a0 (@INSERT a0 y0 (@EMPTY a0)) x0).
Definition term94 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := fun y0 : a0 => (@IN a0 y0 x0) -> Peano.le ((fun y1 : a0 => Nat.mul (x1 y1) (x2 y1)) y0) ((fun y1 : a0 => Nat.mul (@nsum a0 x0 x1) (x2 y1)) y0).
Definition term71 (a0 : Type') (x0 : a0 -> Prop) := and (@FINITE a0 x0).
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : a0 -> nat) := @nsum a0 x0 (fun y0 : a0 => Nat.mul x1 (x2 y0)).
Definition term108 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @SUBSET a0 (@INSERT a0 x0 (@EMPTY a0)) x1.
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> nat) := ((@FINITE a0 x1) /\ (@SUBSET a0 x0 x1)) -> Peano.le (@nsum a0 x0 x2) (@nsum a0 x1 x2).
Definition term77 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) := fun y0 : a0 => (fun y1 : a0 => Nat.mul (x0 y1) (x1 y1)) y0.
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x1) /\ (@SUBSET a0 x0 x1).
Definition term106 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@SUBSET a0 (@INSERT a0 y0 (@EMPTY a0)) x0) = (@IN a0 y0 x0).
Definition term84 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) (x3 : a0) := Nat.mul (@nsum a0 x0 x1) (x2 x3).
Definition term72 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term58 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := Peano.le (@nsum a0 x0 (fun y0 : a0 => Nat.mul (x1 y0) (x2 y0))).
Definition term111 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> Peano.le (@nsum a0 y0 (fun y1 : a0 => Nat.mul (x0 y1) (x1 y1))) (Nat.mul (@nsum a0 y0 x0) (@nsum a0 y0 x1)).
Definition term65 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul x0 y1) (Nat.mul y0 y1)) = ((Peano.le x0 y0) \/ (y1 = (NUMERAL 0))).
Definition term48 (a0 : Type') (x0 : a0 -> nat) := forall y0 : nat, forall y1 : a0 -> Prop, (Nat.mul y0 (@nsum a0 y1 x0)) = (@nsum a0 y1 (fun y2 : a0 => Nat.mul y0 (x0 y2))).
Definition term47 (a0 : Type') (x0 : a0 -> nat) := forall y0 : nat, forall y1 : a0 -> Prop, (@nsum a0 y1 (fun y2 : a0 => Nat.mul y0 (x0 y2))) = (Nat.mul y0 (@nsum a0 y1 x0)).
Definition term73 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term87 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) (x3 : a0) := @eq nat ((fun y0 : a0 => Nat.mul (@nsum a0 x0 x1) (x2 y0)) x3).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> nat) := Peano.le (@nsum a0 x0 x2) (@nsum a0 x1 x2).
Definition term31 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := (forall y0 : a0 -> nat, forall y1 : a0 -> nat, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ (forall y3 : a0, (@IN a0 y3 y2) -> Peano.le (y0 y3) (y1 y3))) -> Peano.le (@nsum a0 y2 y0) (@nsum a0 y2 y1)) -> Peano.le (@nsum a0 x1 x0) (@nsum a0 x1 x2).
Definition term41 (a0 : Type') (x0 : nat) (x1 : a0 -> nat) := fun y0 : a0 -> Prop => (@nsum a0 y0 (fun y1 : a0 => Nat.mul x0 (x1 y1))) = (Nat.mul x0 (@nsum a0 y0 x1)).
Definition term89 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) (x3 : a0) := Peano.le (Nat.mul (x1 x3) (x2 x3)) (Nat.mul (@nsum a0 x0 x1) (x2 x3)).
Definition term59 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := Peano.le (@nsum a0 x1 (fun y0 : a0 => Nat.mul (x0 y0) (x2 y0))) (Nat.mul (@nsum a0 x1 x0) (@nsum a0 x1 x2)).
Definition term21 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := (fun y0 : a0 => (x0 y0) = (@nsum a0 (@INSERT a0 y0 (@EMPTY a0)) x0)) x1.
Definition term76 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) (x2 : a0) := Nat.mul (x0 x2) (x1 x2).
Definition term91 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term80 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) (x2 : a0) := Peano.le ((fun y0 : a0 => Nat.mul (x0 y0) (x1 y0)) x2).
Definition term112 (a0 : Type') (x0 : a0 -> nat) := forall y0 : a0 -> nat, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> Peano.le (@nsum a0 y1 (fun y2 : a0 => Nat.mul (x0 y2) (y0 y2))) (Nat.mul (@nsum a0 y1 x0) (@nsum a0 y1 y0)).
Definition term33 (a0 : Type') (x0 : a0 -> nat) := forall y0 : a0 -> Prop, forall y1 : a0 -> nat, ((@FINITE a0 y0) /\ (forall y2 : a0, (@IN a0 y2 y0) -> Peano.le (x0 y2) (y1 y2))) -> Peano.le (@nsum a0 y0 x0) (@nsum a0 y0 y1).
Definition term24 (a0 : Type') (x0 : a0 -> nat) := forall y0 : a0 -> nat, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (forall y2 : a0, (@IN a0 y2 y1) -> Peano.le (x0 y2) (y0 y2))) -> Peano.le (@nsum a0 y1 x0) (@nsum a0 y1 y0).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0 -> nat, ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> Peano.le (@nsum a0 x0 y1) (@nsum a0 y0 y1).
Definition term75 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) (x2 : a0) := (fun y0 : a0 => Nat.mul (x0 y0) (x1 y0)) x2.
Definition term42 (a0 : Type') (x0 : nat) (x1 : a0 -> nat) := fun y0 : a0 -> Prop => (Nat.mul x0 (@nsum a0 y0 x1)) = (@nsum a0 y0 (fun y1 : a0 => Nat.mul x0 (x1 y1))).
Definition term44 (a0 : Type') (x0 : nat) (x1 : a0 -> nat) := forall y0 : a0 -> Prop, (Nat.mul x0 (@nsum a0 y0 x1)) = (@nsum a0 y0 (fun y1 : a0 => Nat.mul x0 (x1 y1))).
Definition term93 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) (x3 : a0) := (@IN a0 x3 x0) -> (Peano.le (x1 x3) (@nsum a0 x0 x1)) \/ ((x2 x3) = (NUMERAL 0)).
Definition term14 (a0 : Type') (x0 : a0 -> nat) := forall y0 : a0, (@nsum a0 (@INSERT a0 y0 (@EMPTY a0)) x0) = (x0 y0).
Definition term17 (a0 : Type') := fun y0 : a0 -> nat => forall y1 : a0, (y0 y1) = (@nsum a0 (@INSERT a0 y1 (@EMPTY a0)) y0).
Definition term103 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) := Peano.le (@nsum a0 (@INSERT a0 x0 (@EMPTY a0)) x2) (@nsum a0 x1 x2).
Definition term81 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) (x2 : a0) := Peano.le (Nat.mul (x0 x2) (x1 x2)).
Definition term98 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := (@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> Peano.le ((fun y1 : a0 => Nat.mul (x1 y1) (x2 y1)) y0) ((fun y1 : a0 => Nat.mul (@nsum a0 x0 x1) (x2 y1)) y0)).
Definition term29 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := (@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) (x2 y0)).
Definition term45 (a0 : Type') (x0 : a0 -> nat) := fun y0 : nat => forall y1 : a0 -> Prop, (@nsum a0 y1 (fun y2 : a0 => Nat.mul y0 (x0 y2))) = (Nat.mul y0 (@nsum a0 y1 x0)).
Definition term70 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) \/ (x2 = (NUMERAL 0)).
Definition term13 (a0 : Type') (x0 : a0 -> nat) := fun y0 : a0 => (x0 y0) = (@nsum a0 (@INSERT a0 y0 (@EMPTY a0)) x0).
Definition term12 (a0 : Type') (x0 : a0 -> nat) := fun y0 : a0 => (@nsum a0 (@INSERT a0 y0 (@EMPTY a0)) x0) = (x0 y0).
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := ((@FINITE a0 x0) /\ (forall y0 : a0, (@IN a0 y0 x0) -> Peano.le ((fun y1 : a0 => Nat.mul (x1 y1) (x2 y1)) y0) ((fun y1 : a0 => Nat.mul (@nsum a0 x0 x1) (x2 y1)) y0))) -> Peano.le (@nsum a0 x0 (fun y0 : a0 => Nat.mul (x1 y0) (x2 y0))) (@nsum a0 x0 (fun y0 : a0 => Nat.mul (@nsum a0 x0 x1) (x2 y0))).
Definition term32 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) := forall y0 : a0 -> nat, ((@FINITE a0 x1) /\ (forall y1 : a0, (@IN a0 y1 x1) -> Peano.le (x0 y1) (y0 y1))) -> Peano.le (@nsum a0 x1 x0) (@nsum a0 x1 y0).
Definition term26 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (forall y1 : a0, (@IN a0 y1 y0) -> Peano.le (x0 y1) (x1 y1))) -> Peano.le (@nsum a0 y0 x0) (@nsum a0 y0 x1).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0 -> nat, ((@FINITE a0 x1) /\ (@SUBSET a0 x0 x1)) -> Peano.le (@nsum a0 x0 y0) (@nsum a0 x1 y0).
Definition term101 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) := Peano.le (@nsum a0 (@INSERT a0 x0 (@EMPTY a0)) x1).
Definition term43 (a0 : Type') (x0 : nat) (x1 : a0 -> nat) := forall y0 : a0 -> Prop, (@nsum a0 y0 (fun y1 : a0 => Nat.mul x0 (x1 y1))) = (Nat.mul x0 (@nsum a0 y0 x1)).
Definition term19 (a0 : Type') := forall y0 : a0 -> nat, forall y1 : a0, (y0 y1) = (@nsum a0 (@INSERT a0 y1 (@EMPTY a0)) y0).
Definition term18 (a0 : Type') := forall y0 : a0 -> nat, forall y1 : a0, (@nsum a0 (@INSERT a0 y1 (@EMPTY a0)) y0) = (y0 y1).
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := fun y0 : a0 => Nat.mul (@nsum a0 x0 x1) (x2 y0).
Definition term11 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) := @nsum a0 (@INSERT a0 x0 (@EMPTY a0)) x1.
Definition term57 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := @nsum a0 x0 (fun y0 : a0 => Nat.mul (@nsum a0 x0 x1) (x2 y0)).
