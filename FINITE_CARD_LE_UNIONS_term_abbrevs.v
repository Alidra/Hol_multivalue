Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term121 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term163 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : nat) (x3 : nat) := (@FINITE a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 (@IN a0 y1 x0) (x1 y1))))) /\ (Peano.le (@CARD a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 (@IN a0 y1 x0) (x1 y1))))) (Nat.mul x2 x3)).
Definition term109 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := Peano.le (@CARD a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 (@IN a0 y1 x0) (x1 y1))))).
Definition term16 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> Prop, (@GSPEC a1 (fun y1 : a1 => exists y2 : a0, @SETSPEC a1 y1 (@IN a0 y2 y0) (x0 y2))) = (@IMAGE a0 a1 x0 y0).
Definition term63 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : type1413 a0 a1) (x3 : a0) := @SETSPEC (a1 -> Prop) x0 (@IN a0 x3 x1) (x2 x3).
Definition term49 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := @FINITE (a1 -> Prop) (@GSPEC (a1 -> Prop) (fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 (@IN a0 y1 x0) (x1 y1))).
Definition term41 (a0 : Type') (x0 : type686 a0) := (@FINITE (a0 -> Prop) x0) /\ (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> @FINITE a0 y0).
Definition term130 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le (Nat.mul y0 y2) (Nat.mul y1 y2)) = ((Peano.le y0 y1) \/ (y2 = (NUMERAL 0)))) x0.
Definition term113 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) x0.
Definition term43 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : a0) (x3 : nat) := (@IN a0 x2 x0) -> (@FINITE a1 (x1 x2)) /\ (Peano.le (@CARD a1 (x1 x2)) x3).
Definition term162 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0 -> Prop) (x2 : nat) (x3 : nat) := fun y0 : nat => (Peano.le (@CARD a1 (@UNIONS a1 (@IMAGE a0 (a1 -> Prop) x0 x1))) y0) /\ (Peano.le y0 (Nat.mul x2 x3)).
Definition term31 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> @FINITE a1 (@IMAGE a0 a1 x0 x1).
Definition term126 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term104 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term62 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : type1413 a0 a1) (x3 : a0) := @SETSPEC (a1 -> Prop) x0 ((fun y0 : a0 => @IN a0 y0 x1) x3) (x2 x3).
Definition term97 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := ((@IN a0 x1 x2) = (@IN a0 x1 x2)) -> ((@IN a0 x1 x2) -> (@FINITE a1 (x0 x1)) = x3) -> ((@IN a0 x1 x2) -> @FINITE a1 (x0 x1)) = ((@IN a0 x1 x2) -> x3).
Definition term168 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, forall y1 : type1413 a0 a1, forall y2 : nat, forall y3 : nat, ((forall y4 : a0, (@IN a0 y4 y0) -> (@FINITE a1 (y1 y4)) /\ (Peano.le (@CARD a1 (y1 y4)) y3)) /\ ((@FINITE a0 y0) /\ (Peano.le (@CARD a0 y0) y2))) -> (@FINITE a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y4 : a1 -> Prop => exists y5 : a0, @SETSPEC (a1 -> Prop) y4 (@IN a0 y5 y0) (y1 y5))))) /\ (Peano.le (@CARD a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y4 : a1 -> Prop => exists y5 : a0, @SETSPEC (a1 -> Prop) y4 (@IN a0 y5 y0) (y1 y5))))) (Nat.mul y2 y3)).
Definition term167 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : type1413 a0 a1, forall y1 : nat, forall y2 : nat, ((forall y3 : a0, (@IN a0 y3 x0) -> (@FINITE a1 (y0 y3)) /\ (Peano.le (@CARD a1 (y0 y3)) y2)) /\ ((@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) y1))) -> (@FINITE a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y3 : a1 -> Prop => exists y4 : a0, @SETSPEC (a1 -> Prop) y3 (@IN a0 y4 x0) (y0 y4))))) /\ (Peano.le (@CARD a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y3 : a1 -> Prop => exists y4 : a0, @SETSPEC (a1 -> Prop) y3 (@IN a0 y4 x0) (y0 y4))))) (Nat.mul y1 y2)).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := forall y0 : type1413 a0 a1, forall y1 : nat, forall y2 : nat, ((@HAS_SIZE a0 x0 y1) /\ (forall y3 : a0, (@IN a0 y3 x0) -> (@FINITE a1 (y0 y3)) /\ (Peano.le (@CARD a1 (y0 y3)) y2))) -> Peano.le (@CARD a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y3 : a1 -> Prop => exists y4 : a0, @SETSPEC (a1 -> Prop) y3 (@IN a0 y4 x0) (y0 y4))))) (Nat.mul y1 y2).
Definition term0 (a0 : Type') (a1 : Type') := forall y0 : a0 -> Prop, forall y1 : type1413 a0 a1, forall y2 : nat, forall y3 : nat, ((@HAS_SIZE a0 y0 y2) /\ (forall y4 : a0, (@IN a0 y4 y0) -> (@FINITE a1 (y1 y4)) /\ (Peano.le (@CARD a1 (y1 y4)) y3))) -> Peano.le (@CARD a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y4 : a1 -> Prop => exists y5 : a0, @SETSPEC (a1 -> Prop) y4 (@IN a0 y5 y0) (y1 y5))))) (Nat.mul y2 y3).
Definition term164 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : nat) (x3 : nat) := ((forall y0 : a0, (@IN a0 y0 x0) -> (@FINITE a1 (x1 y0)) /\ (Peano.le (@CARD a1 (x1 y0)) x3)) /\ ((@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) x2))) -> (@FINITE a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 (@IN a0 y1 x0) (x1 y1))))) /\ (Peano.le (@CARD a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 (@IN a0 y1 x0) (x1 y1))))) (Nat.mul x2 x3)).
Definition term135 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 x2) (Nat.mul x1 x2).
Definition term103 (a0 : Type') := forall y0 : a0, True.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : type1413 a0 a1, forall y2 : nat, forall y3 : nat, ((@HAS_SIZE a0 y0 y2) /\ (forall y4 : a0, (@IN a0 y4 y0) -> (@FINITE a1 (y1 y4)) /\ (Peano.le (@CARD a1 (y1 y4)) y3))) -> Peano.le (@CARD a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y4 : a1 -> Prop => exists y5 : a0, @SETSPEC (a1 -> Prop) y4 (@IN a0 y5 y0) (y1 y5))))) (Nat.mul y2 y3)) x0.
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((@HAS_SIZE a0 x0 x2) /\ (forall y1 : a0, (@IN a0 y1 x0) -> (@FINITE a1 (x1 y1)) /\ (Peano.le (@CARD a1 (x1 y1)) y0))) -> Peano.le (@CARD a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y1 : a1 -> Prop => exists y2 : a0, @SETSPEC (a1 -> Prop) y1 (@IN a0 y2 x0) (x1 y2))))) (Nat.mul x2 y0)) x3.
Definition term84 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : a0) := ((fun y0 : a0 => @IN a0 y0 x0) x2) -> @FINITE a1 (x1 x2).
Definition term120 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2) -> Peano.le x0 x1.
Definition term134 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le (Nat.mul x0 y0) (Nat.mul x1 y0)) = ((Peano.le x0 x1) \/ (y0 = (NUMERAL 0)))) x2.
Definition term101 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 x1) -> True.
Definition term46 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := @FINITE a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 (@IN a0 y1 x0) (x1 y1)))).
Definition term76 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : a1 -> Prop) := (@IN (a1 -> Prop) x2 (@GSPEC (a1 -> Prop) (fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 (@IN a0 y1 x0) (x1 y1)))) -> @FINITE a1 x2.
Definition term75 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : a1 -> Prop) := (@IN (a1 -> Prop) x2 (@GSPEC (a1 -> Prop) (fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 ((fun y2 : a0 => @IN a0 y2 x0) y1) (x1 y1)))) -> @FINITE a1 x2.
Definition term124 (x0 : nat) := forall y0 : nat, (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0.
Definition term59 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => @IN a0 y0 x0) x1.
Definition term12 (a0 : Type') (a1 : Type') := (forall y0 : a0 -> Prop, forall y1 : type1413 a0 a1, forall y2 : nat, forall y3 : nat, ((@HAS_SIZE a0 y0 y2) /\ (forall y4 : a0, (@IN a0 y4 y0) -> (@FINITE a1 (y1 y4)) /\ (Peano.le (@CARD a1 (y1 y4)) y3))) -> Peano.le (@CARD a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y4 : a1 -> Prop => exists y5 : a0, @SETSPEC (a1 -> Prop) y4 (@IN a0 y5 y0) (y1 y5))))) (Nat.mul y2 y3)) -> forall y0 : a0 -> Prop, forall y1 : type1413 a0 a1, forall y2 : nat, forall y3 : nat, ((@HAS_SIZE a0 y0 y2) /\ (forall y4 : a0, (@IN a0 y4 y0) -> (@FINITE a1 (y1 y4)) /\ (Peano.le (@CARD a1 (y1 y4)) y3))) -> Peano.le (@CARD a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y4 : a1 -> Prop => exists y5 : a0, @SETSPEC (a1 -> Prop) y4 (@IN a0 y5 y0) (y1 y5))))) (Nat.mul y2 y3).
Definition term87 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := fun y0 : a0 => (@IN a0 y0 x0) -> @FINITE a1 (x1 y0).
Definition term105 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := @UNIONS a1 (@GSPEC (a1 -> Prop) (fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 (@IN a0 y1 x0) (x1 y1))).
Definition term117 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0) x2.
Definition term29 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> @FINITE a1 (@IMAGE a0 a1 x0 y0).
Definition term93 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : a0) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@IN a0 x2 x0) = y0) -> (y0 -> (@FINITE a1 (x1 x2)) = y1) -> ((@IN a0 x2 x0) -> @FINITE a1 (x1 x2)) = (y0 -> y1)) x3.
Definition term107 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := @CARD a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 (@IN a0 y1 x0) (x1 y1)))).
Definition term36 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0 -> a1) := (fun y0 : a0 -> a1 => (forall y1 : a1, (@IN a1 y1 (@GSPEC a1 (fun y2 : a1 => exists y3 : a0, @SETSPEC a1 y2 (x0 y3) (y0 y3)))) -> x1 y1) = (forall y1 : a0, (x0 y1) -> x1 (y0 y1))) x2.
Definition term133 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le (Nat.mul x0 y0) (Nat.mul x1 y0)) = ((Peano.le x0 x1) \/ (y0 = (NUMERAL 0))).
Definition term132 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (Nat.mul x0 y1) (Nat.mul y0 y1)) = ((Peano.le x0 y0) \/ (y1 = (NUMERAL 0)))) x1.
Definition term115 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1) x1.
Definition term34 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> a1, (forall y2 : a1, (@IN a1 y2 (@GSPEC a1 (fun y3 : a1 => exists y4 : a0, @SETSPEC a1 y3 (y0 y4) (y1 y4)))) -> x0 y2) = (forall y2 : a0, (y0 y2) -> x0 (y1 y2))) x1.
Definition term27 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@GSPEC a1 (fun y1 : a1 => exists y2 : a0, @SETSPEC a1 y1 (@IN a0 y2 y0) (x0 y2))) = (@IMAGE a0 a1 x0 y0)) x1.
Definition term148 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0 -> Prop) (x2 : nat) (x3 : nat) := (Peano.le (@CARD a1 (@UNIONS a1 (@IMAGE a0 (a1 -> Prop) x0 x1))) (Nat.mul (@CARD a0 x1) x3)) /\ (Peano.le (Nat.mul (@CARD a0 x1) x3) (Nat.mul x2 x3)).
Definition term35 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := forall y0 : a0 -> a1, (forall y1 : a1, (@IN a1 y1 (@GSPEC a1 (fun y2 : a1 => exists y3 : a0, @SETSPEC a1 y2 (x0 y3) (y0 y3)))) -> x1 y1) = (forall y1 : a0, (x0 y1) -> x1 (y0 y1)).
Definition term157 (a0 : Type') (x0 : a0 -> Prop) := and (@FINITE a0 x0).
Definition term66 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : type1413 a0 a1) := exists y0 : a0, @SETSPEC (a1 -> Prop) x0 ((fun y1 : a0 => @IN a0 y1 x1) y0) (x2 y0).
Definition term89 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term138 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@IMAGE a0 a1 x0 y0) = (@GSPEC a1 (fun y1 : a1 => exists y2 : a0, @SETSPEC a1 y1 (@IN a0 y2 y0) (x0 y2)))) x1.
Definition term60 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := @SETSPEC (a1 -> Prop) x0 ((fun y0 : a0 => @IN a0 y0 x1) x2).
Definition term74 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : type1413 a0 a1) := imp (@IN (a1 -> Prop) x0 (@GSPEC (a1 -> Prop) (fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 (@IN a0 y1 x1) (x2 y1)))).
Definition term73 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : type1413 a0 a1) := imp (@IN (a1 -> Prop) x0 (@GSPEC (a1 -> Prop) (fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 ((fun y2 : a0 => @IN a0 y2 x1) y1) (x2 y1)))).
Definition term96 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : a0) (x3 : Prop) (x4 : Prop) := ((@IN a0 x2 x0) = x3) -> (x3 -> (@FINITE a1 (x1 x2)) = x4) -> ((@IN a0 x2 x0) -> @FINITE a1 (x1 x2)) = (x3 -> x4).
Definition term118 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x0) /\ (Peano.le x0 x2)) -> Peano.le x1 x2.
Definition term149 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0 -> Prop) (x2 : nat) := (Peano.le (@CARD a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 (@IN a0 y1 x1) (x0 y1))))) (Nat.mul (@CARD a0 x1) x2)) /\ True.
Definition term146 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := or (Peano.le (@CARD a0 x0) x1).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => forall y1 : nat, forall y2 : nat, ((@HAS_SIZE a0 x0 y1) /\ (forall y3 : a0, (@IN a0 y3 x0) -> (@FINITE a1 (y0 y3)) /\ (Peano.le (@CARD a1 (y0 y3)) y2))) -> Peano.le (@CARD a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y3 : a1 -> Prop => exists y4 : a0, @SETSPEC (a1 -> Prop) y3 (@IN a0 y4 x0) (y0 y4))))) (Nat.mul y1 y2)) x1.
Definition term37 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) (x2 : a1 -> Prop) := forall y0 : a1, (@IN a1 y0 (@GSPEC a1 (fun y1 : a1 => exists y2 : a0, @SETSPEC a1 y1 (x0 y2) (x1 y2)))) -> x2 y0.
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 -> Prop => (@GSPEC a1 (fun y1 : a1 => exists y2 : a0, @SETSPEC a1 y1 (@IN a0 y2 y0) (x0 y2))) = (@IMAGE a0 a1 x0 y0).
Definition term153 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (fun y0 : nat => (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0))) x1.
Definition term106 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0 -> Prop) := @UNIONS a1 (@IMAGE a0 (a1 -> Prop) x0 x1).
Definition term110 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0 -> Prop) := Peano.le (@CARD a1 (@UNIONS a1 (@IMAGE a0 (a1 -> Prop) x0 x1))).
Definition term55 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type686 a1) (x2 : type1413 a0 a1) := forall y0 : a0, (x0 y0) -> x1 (x2 y0).
Definition term38 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a0 -> a1) := forall y0 : a0, (x0 y0) -> x1 (x2 y0).
Definition term78 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := fun y0 : a1 -> Prop => (@IN (a1 -> Prop) y0 (@GSPEC (a1 -> Prop) (fun y1 : a1 -> Prop => exists y2 : a0, @SETSPEC (a1 -> Prop) y1 (@IN a0 y2 x0) (x1 y2)))) -> @FINITE a1 y0.
Definition term77 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := fun y0 : a1 -> Prop => (@IN (a1 -> Prop) y0 (@GSPEC (a1 -> Prop) (fun y1 : a1 -> Prop => exists y2 : a0, @SETSPEC (a1 -> Prop) y1 ((fun y3 : a0 => @IN a0 y3 x0) y2) (x1 y2)))) -> @FINITE a1 y0.
Definition term15 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := fun y0 : a0 -> Prop => (@IMAGE a0 a1 x0 y0) = (@GSPEC a1 (fun y1 : a1 => exists y2 : a0, @SETSPEC a1 y1 (@IN a0 y2 y0) (x0 y2))).
Definition term166 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := forall y0 : nat, forall y1 : nat, ((forall y2 : a0, (@IN a0 y2 x0) -> (@FINITE a1 (x1 y2)) /\ (Peano.le (@CARD a1 (x1 y2)) y1)) /\ ((@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) y0))) -> (@FINITE a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y2 : a1 -> Prop => exists y3 : a0, @SETSPEC (a1 -> Prop) y2 (@IN a0 y3 x0) (x1 y3))))) /\ (Peano.le (@CARD a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y2 : a1 -> Prop => exists y3 : a0, @SETSPEC (a1 -> Prop) y2 (@IN a0 y3 x0) (x1 y3))))) (Nat.mul y0 y1)).
Definition term131 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le (Nat.mul x0 y1) (Nat.mul y0 y1)) = ((Peano.le x0 y0) \/ (y1 = (NUMERAL 0))).
Definition term125 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1.
Definition term114 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 y1)) -> Peano.le x0 y1.
Definition term112 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y2)) -> Peano.le y0 y2.
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := forall y0 : nat, forall y1 : nat, ((@HAS_SIZE a0 x0 y0) /\ (forall y2 : a0, (@IN a0 y2 x0) -> (@FINITE a1 (x1 y2)) /\ (Peano.le (@CARD a1 (x1 y2)) y1))) -> Peano.le (@CARD a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y2 : a1 -> Prop => exists y3 : a0, @SETSPEC (a1 -> Prop) y2 (@IN a0 y3 x0) (x1 y3))))) (Nat.mul y0 y1).
Definition term102 (a0 : Type') := fun y0 : a0 => True.
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((@HAS_SIZE a0 x0 y0) /\ (forall y2 : a0, (@IN a0 y2 x0) -> (@FINITE a1 (x1 y2)) /\ (Peano.le (@CARD a1 (x1 y2)) y1))) -> Peano.le (@CARD a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y2 : a1 -> Prop => exists y3 : a0, @SETSPEC (a1 -> Prop) y2 (@IN a0 y3 x0) (x1 y3))))) (Nat.mul y0 y1)) x2.
Definition term144 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul (@CARD a0 x0) x2) (Nat.mul x1 x2).
Definition term159 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : nat) := fun y0 : a0 => (@IN a0 y0 x0) -> (@FINITE a1 (x1 y0)) /\ (Peano.le (@CARD a1 (x1 y0)) x2).
Definition term156 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) /\ ((@CARD a0 x0) = (@CARD a0 x0)).
Definition term145 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) (x2 : nat) := (Peano.le (@CARD a0 x0) x1) \/ (x2 = (NUMERAL 0)).
Definition term161 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0 -> Prop) (x2 : nat) (x3 : nat) := exists y0 : nat, (Peano.le (@CARD a1 (@UNIONS a1 (@IMAGE a0 (a1 -> Prop) x0 x1))) y0) /\ (Peano.le y0 (Nat.mul x2 x3)).
Definition term108 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0 -> Prop) := @CARD a1 (@UNIONS a1 (@IMAGE a0 (a1 -> Prop) x0 x1)).
Definition term69 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 (@IN a0 y1 x0) (x1 y1).
Definition term68 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 ((fun y2 : a0 => @IN a0 y2 x0) y1) (x1 y1).
Definition term160 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : nat) := (@HAS_SIZE a0 x0 (@CARD a0 x0)) /\ (forall y0 : a0, (@IN a0 y0 x0) -> (@FINITE a1 (x1 y0)) /\ (Peano.le (@CARD a1 (x1 y0)) x2)).
Definition term86 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := fun y0 : a0 => ((fun y1 : a0 => @IN a0 y1 x0) y0) -> @FINITE a1 (x1 y0).
Definition term61 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := @SETSPEC (a1 -> Prop) x0 (@IN a0 x1 x2).
Definition term57 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := forall y0 : a0, ((fun y1 : a0 => @IN a0 y1 x0) y0) -> @FINITE a1 (x1 y0).
Definition term151 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) x0.
Definition term58 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => @IN a0 y0 x0.
Definition term50 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0 -> Prop) := @FINITE (a1 -> Prop) (@IMAGE a0 (a1 -> Prop) x0 x1).
Definition term32 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := @FINITE a1 (@IMAGE a0 a1 x0 x1).
Definition term140 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0 -> Prop) (x2 : nat) := Peano.le (@CARD a1 (@UNIONS a1 (@IMAGE a0 (a1 -> Prop) x0 x1))) (Nat.mul (@CARD a0 x1) x2).
Definition term94 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : a0) (x3 : Prop) := forall y0 : Prop, ((@IN a0 x2 x0) = x3) -> (x3 -> (@FINITE a1 (x1 x2)) = y0) -> ((@IN a0 x2 x0) -> @FINITE a1 (x1 x2)) = (x3 -> y0).
Definition term90 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term82 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp ((fun y0 : a0 => @IN a0 y0 x0) x1).
Definition term158 (a0 : Type') (x0 : a0 -> Prop) := and (@HAS_SIZE a0 x0 (@CARD a0 x0)).
Definition term81 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := @eq Prop (forall y0 : a1 -> Prop, (@IN (a1 -> Prop) y0 (@GSPEC (a1 -> Prop) (fun y1 : a1 -> Prop => exists y2 : a0, @SETSPEC (a1 -> Prop) y1 (@IN a0 y2 x0) (x1 y2)))) -> @FINITE a1 y0).
Definition term80 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := @eq Prop (forall y0 : a1 -> Prop, (@IN (a1 -> Prop) y0 (@GSPEC (a1 -> Prop) (fun y1 : a1 -> Prop => exists y2 : a0, @SETSPEC (a1 -> Prop) y1 ((fun y3 : a0 => @IN a0 y3 x0) y2) (x1 y2)))) -> @FINITE a1 y0).
Definition term30 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> @FINITE a1 (@IMAGE a0 a1 x0 y0)) x1.
Definition term111 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0 -> Prop) (x2 : nat) (x3 : nat) := Peano.le (@CARD a1 (@UNIONS a1 (@IMAGE a0 (a1 -> Prop) x0 x1))) (Nat.mul x2 x3).
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : nat) (x3 : nat) := Peano.le (@CARD a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 (@IN a0 y1 x0) (x1 y1))))) (Nat.mul x2 x3).
Definition term65 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : type1413 a0 a1) := fun y0 : a0 => @SETSPEC (a1 -> Prop) x0 (@IN a0 y0 x1) (x2 y0).
Definition term143 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0 -> Prop) (x2 : nat) := and (Peano.le (@CARD a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 (@IN a0 y1 x1) (x0 y1))))) (Nat.mul (@CARD a0 x1) x2)).
Definition term142 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0 -> Prop) (x2 : nat) := and (Peano.le (@CARD a1 (@UNIONS a1 (@IMAGE a0 (a1 -> Prop) x0 x1))) (Nat.mul (@CARD a0 x1) x2)).
Definition term54 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : type686 a1) := forall y0 : a1 -> Prop, (@IN (a1 -> Prop) y0 (@GSPEC (a1 -> Prop) (fun y1 : a1 -> Prop => exists y2 : a0, @SETSPEC (a1 -> Prop) y1 (x0 y2) (x1 y2)))) -> x2 y0.
Definition term154 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) /\ ((@CARD a0 x0) = x1).
Definition term92 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : a0) := forall y0 : Prop, forall y1 : Prop, ((@IN a0 x2 x0) = y0) -> (y0 -> (@FINITE a1 (x1 x2)) = y1) -> ((@IN a0 x2 x0) -> @FINITE a1 (x1 x2)) = (y0 -> y1).
Definition term91 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term83 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term42 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : nat) (x3 : a0) := (fun y0 : a0 => (@IN a0 y0 x0) -> (@FINITE a1 (x1 y0)) /\ (Peano.le (@CARD a1 (x1 y0)) x2)) x3.
Definition term139 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := Nat.mul (@CARD a0 x0) x1.
Definition term116 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x1 x0) /\ (Peano.le x0 y0)) -> Peano.le x1 y0.
Definition term33 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0 -> a1, (forall y2 : a1, (@IN a1 y2 (@GSPEC a1 (fun y3 : a1 => exists y4 : a0, @SETSPEC a1 y3 (y0 y4) (y1 y4)))) -> x0 y2) = (forall y2 : a0, (y0 y2) -> x0 (y1 y2)).
Definition term21 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, forall y1 : a0 -> Prop, (@IMAGE a0 a1 y0 y1) = (@GSPEC a1 (fun y2 : a1 => exists y3 : a0, @SETSPEC a1 y2 (@IN a0 y3 y1) (y0 y3))).
Definition term20 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, forall y1 : a0 -> Prop, (@GSPEC a1 (fun y2 : a1 => exists y3 : a0, @SETSPEC a1 y2 (@IN a0 y3 y1) (y0 y3))) = (@IMAGE a0 a1 y0 y1).
Definition term95 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : a0) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((@IN a0 x2 x0) = x3) -> (x3 -> (@FINITE a1 (x1 x2)) = y0) -> ((@IN a0 x2 x0) -> @FINITE a1 (x1 x2)) = (x3 -> y0)) x4.
Definition term44 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) (x2 : nat) := (@FINITE a1 (x0 x1)) /\ (Peano.le (@CARD a1 (x0 x1)) x2).
Definition term17 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> Prop, (@IMAGE a0 a1 x0 y0) = (@GSPEC a1 (fun y1 : a1 => exists y2 : a0, @SETSPEC a1 y1 (@IN a0 y2 y0) (x0 y2))).
Definition term150 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0 -> Prop) (x2 : nat) := ((@HAS_SIZE a0 x1 (@CARD a0 x1)) /\ (forall y0 : a0, (@IN a0 y0 x1) -> (@FINITE a1 (x0 y0)) /\ (Peano.le (@CARD a1 (x0 y0)) x2))) -> Peano.le (@CARD a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 (@IN a0 y1 x1) (x0 y1))))) (Nat.mul (@CARD a0 x1) x2).
Definition term52 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> (@FINITE (a1 -> Prop) (@IMAGE a0 (a1 -> Prop) x0 x1)) = True.
Definition term51 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> (@FINITE a1 (@IMAGE a0 a1 x0 x1)) = True.
Definition term39 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => (@FINITE a0 (@UNIONS a0 y0)) = ((@FINITE (a0 -> Prop) y0) /\ (forall y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 y0) -> @FINITE a0 y1))) x0.
Definition term127 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (Peano.le y0 y2) /\ (Peano.le y2 y1)) -> Peano.le y0 y1) x0.
Definition term147 (x0 : nat) := True \/ (x0 = (NUMERAL 0)).
Definition term88 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := forall y0 : a0, (@IN a0 y0 x0) -> @FINITE a1 (x1 y0).
Definition term45 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) := @FINITE a1 (x0 x1).
Definition term119 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : nat) := forall y0 : nat, ((@HAS_SIZE a0 x0 x2) /\ (forall y1 : a0, (@IN a0 y1 x0) -> (@FINITE a1 (x1 y1)) /\ (Peano.le (@CARD a1 (x1 y1)) y0))) -> Peano.le (@CARD a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y1 : a1 -> Prop => exists y2 : a0, @SETSPEC (a1 -> Prop) y1 (@IN a0 y2 x0) (x1 y2))))) (Nat.mul x2 y0).
Definition term99 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : a0) := (@IN a0 x2 x0) -> (@FINITE a1 (x1 x2)) = True.
Definition term152 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : nat, (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0)).
Definition term79 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := forall y0 : a1 -> Prop, (@IN (a1 -> Prop) y0 (@GSPEC (a1 -> Prop) (fun y1 : a1 -> Prop => exists y2 : a0, @SETSPEC (a1 -> Prop) y1 (@IN a0 y2 x0) (x1 y2)))) -> @FINITE a1 y0.
Definition term56 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := forall y0 : a1 -> Prop, (@IN (a1 -> Prop) y0 (@GSPEC (a1 -> Prop) (fun y1 : a1 -> Prop => exists y2 : a0, @SETSPEC (a1 -> Prop) y1 ((fun y3 : a0 => @IN a0 y3 x0) y2) (x1 y2)))) -> @FINITE a1 y0.
Definition term98 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := ((@IN a0 x1 x2) -> (@FINITE a1 (x0 x1)) = x3) -> ((@IN a0 x1 x2) -> @FINITE a1 (x0 x1)) = ((@IN a0 x1 x2) -> x3).
Definition term72 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : type1413 a0 a1) := @IN (a1 -> Prop) x0 (@GSPEC (a1 -> Prop) (fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 (@IN a0 y1 x1) (x2 y1))).
Definition term71 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : type1413 a0 a1) := @IN (a1 -> Prop) x0 (@GSPEC (a1 -> Prop) (fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 ((fun y2 : a0 => @IN a0 y2 x1) y1) (x2 y1))).
Definition term123 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.le x0 y0) /\ (Peano.le y0 x1)) -> Peano.le x0 x1.
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : nat) (x3 : nat) := ((@HAS_SIZE a0 x0 x2) /\ (forall y0 : a0, (@IN a0 y0 x0) -> (@FINITE a1 (x1 y0)) /\ (Peano.le (@CARD a1 (x1 y0)) x3))) -> Peano.le (@CARD a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 (@IN a0 y1 x0) (x1 y1))))) (Nat.mul x2 x3).
Definition term47 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := (@FINITE (a1 -> Prop) (@GSPEC (a1 -> Prop) (fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 (@IN a0 y1 x0) (x1 y1)))) /\ (forall y0 : a1 -> Prop, (@IN (a1 -> Prop) y0 (@GSPEC (a1 -> Prop) (fun y1 : a1 -> Prop => exists y2 : a0, @SETSPEC (a1 -> Prop) y1 (@IN a0 y2 x0) (x1 y2)))) -> @FINITE a1 y0).
Definition term100 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0) (x2 : a0 -> Prop) := ((@IN a0 x1 x2) -> (@FINITE a1 (x0 x1)) = True) -> ((@IN a0 x1 x2) -> @FINITE a1 (x0 x1)) = ((@IN a0 x1 x2) -> True).
Definition term24 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : nat) := forall y0 : a0, (@IN a0 y0 x0) -> (@FINITE a1 (x1 y0)) /\ (Peano.le (@CARD a1 (x1 y0)) x2).
Definition term18 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, (@GSPEC a1 (fun y2 : a1 => exists y3 : a0, @SETSPEC a1 y2 (@IN a0 y3 y1) (y0 y3))) = (@IMAGE a0 a1 y0 y1).
Definition term136 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) \/ (x2 = (NUMERAL 0)).
Definition term122 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.le x0 y0) /\ (Peano.le y0 x1).
Definition term22 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : nat) (x2 : a0 -> Prop) (x3 : nat) := (forall y0 : a0, (@IN a0 y0 x2) -> (@FINITE a1 (x0 y0)) /\ (Peano.le (@CARD a1 (x0 y0)) x1)) /\ ((@FINITE a0 x2) /\ (Peano.le (@CARD a0 x2) x3)).
Definition term85 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : a0) := (@IN a0 x2 x0) -> @FINITE a1 (x1 x2).
Definition term141 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0 -> Prop) (x2 : nat) := Peano.le (@CARD a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 (@IN a0 y1 x1) (x0 y1))))) (Nat.mul (@CARD a0 x1) x2).
Definition term165 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : nat) := forall y0 : nat, ((forall y1 : a0, (@IN a0 y1 x0) -> (@FINITE a1 (x1 y1)) /\ (Peano.le (@CARD a1 (x1 y1)) y0)) /\ ((@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) x2))) -> (@FINITE a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y1 : a1 -> Prop => exists y2 : a0, @SETSPEC (a1 -> Prop) y1 (@IN a0 y2 x0) (x1 y2))))) /\ (Peano.le (@CARD a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y1 : a1 -> Prop => exists y2 : a0, @SETSPEC (a1 -> Prop) y1 (@IN a0 y2 x0) (x1 y2))))) (Nat.mul x2 y0)).
Definition term40 (a0 : Type') (x0 : type686 a0) := @FINITE a0 (@UNIONS a0 x0).
Definition term23 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) /\ (Peano.le (@CARD a0 x0) x1).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := @GSPEC a1 (fun y0 : a1 => exists y1 : a0, @SETSPEC a1 y0 (@IN a0 y1 x0) (x1 y1)).
Definition term137 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, (@IMAGE a0 a1 y0 y1) = (@GSPEC a1 (fun y2 : a1 => exists y3 : a0, @SETSPEC a1 y2 (@IN a0 y3 y1) (y0 y3)))) x0.
Definition term28 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> @FINITE a1 (@IMAGE a0 a1 y0 y1)) x0.
Definition term26 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, (@GSPEC a1 (fun y2 : a1 => exists y3 : a0, @SETSPEC a1 y2 (@IN a0 y3 y1) (y0 y3))) = (@IMAGE a0 a1 y0 y1)) x0.
Definition term155 (a0 : Type') (x0 : a0 -> Prop) := @HAS_SIZE a0 x0 (@CARD a0 x0).
Definition term53 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := and (@FINITE (a1 -> Prop) (@GSPEC (a1 -> Prop) (fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 (@IN a0 y1 x0) (x1 y1)))).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := Peano.le (@CARD a0 x0) x1.
Definition term19 (a0 : Type') (a1 : Type') := fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, (@IMAGE a0 a1 y0 y1) = (@GSPEC a1 (fun y2 : a1 => exists y3 : a0, @SETSPEC a1 y2 (@IN a0 y3 y1) (y0 y3))).
Definition term67 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : type1413 a0 a1) := exists y0 : a0, @SETSPEC (a1 -> Prop) x0 (@IN a0 y0 x1) (x2 y0).
Definition term70 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := @GSPEC (a1 -> Prop) (fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 ((fun y2 : a0 => @IN a0 y2 x0) y1) (x1 y1)).
Definition term48 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) := @GSPEC (a1 -> Prop) (fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 (@IN a0 y1 x0) (x1 y1)).
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : type1413 a0 a1) (x2 : nat) (x3 : nat) := (forall y0 : a0 -> Prop, forall y1 : type1413 a0 a1, forall y2 : nat, forall y3 : nat, ((@HAS_SIZE a0 y0 y2) /\ (forall y4 : a0, (@IN a0 y4 y0) -> (@FINITE a1 (y1 y4)) /\ (Peano.le (@CARD a1 (y1 y4)) y3))) -> Peano.le (@CARD a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y4 : a1 -> Prop => exists y5 : a0, @SETSPEC (a1 -> Prop) y4 (@IN a0 y5 y0) (y1 y5))))) (Nat.mul y2 y3)) -> Peano.le (@CARD a1 (@UNIONS a1 (@GSPEC (a1 -> Prop) (fun y0 : a1 -> Prop => exists y1 : a0, @SETSPEC (a1 -> Prop) y0 (@IN a0 y1 x0) (x1 y1))))) (Nat.mul x2 x3).
Definition term129 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) (x1 : a0 -> Prop) (x2 : nat) (x3 : nat) := (exists y0 : nat, (Peano.le (@CARD a1 (@UNIONS a1 (@IMAGE a0 (a1 -> Prop) x0 x1))) y0) /\ (Peano.le y0 (Nat.mul x2 x3))) -> Peano.le (@CARD a1 (@UNIONS a1 (@IMAGE a0 (a1 -> Prop) x0 x1))) (Nat.mul x2 x3).
Definition term64 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : type1413 a0 a1) := fun y0 : a0 => @SETSPEC (a1 -> Prop) x0 ((fun y1 : a0 => @IN a0 y1 x1) y0) (x2 y0).
Definition term128 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.le x0 y1) /\ (Peano.le y1 y0)) -> Peano.le x0 y0) x1.
Definition term9 (a0 : Type') (a1 : Type') (x0 : nat) (x1 : a0 -> Prop) (x2 : type1413 a0 a1) (x3 : nat) := (@HAS_SIZE a0 x1 x0) /\ (forall y0 : a0, (@IN a0 y0 x1) -> (@FINITE a1 (x2 y0)) /\ (Peano.le (@CARD a1 (x2 y0)) x3)).