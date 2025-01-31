Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term26 (x0 : nat) (x1 : nat) := exists y0 : nat, (Peano.lt x0 y0) /\ (Peano.le y0 x1).
Definition term137 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@nsum a0 y1 (fun y2 : a0 => y0)) = (Nat.mul (@CARD a0 y1) y0)) x0.
Definition term130 := (~ False) -> False.
Definition term43 (a0 : Type') (x0 : nat) := fun y0 : a0 => x0.
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x0 x1) /\ (Peano.le x1 x2).
Definition term92 (a0 : Type') (x0 : a0 -> Prop) := imp (@FINITE a0 x0).
Definition term88 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) (x3 : nat) := (@IN a0 x0 x1) -> (Peano.lt (x2 x0) x3) -> exists y0 : a0, (@IN a0 y0 x1) /\ (Peano.lt (x2 y0) x3).
Definition term83 (x0 : Prop) := ~ (~ x0).
Definition term18 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) x0.
Definition term37 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) x2.
Definition term31 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.lt y0 y2) /\ (Peano.le y2 y1)) -> Peano.lt y0 y1.
Definition term63 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term126 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) (x2 : nat) := ~ (Peano.lt (x0 x1) x2).
Definition term113 (a0 : Type') (x0 : a0 -> Prop) := ~ (ex x0).
Definition term153 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> nat, forall y2 : nat, ((@FINITE a0 y0) /\ ((forall y3 : a0, (@IN a0 y3 y0) -> Peano.le (y1 y3) y2) /\ (exists y3 : a0, (@IN a0 y3 y0) /\ (Peano.lt (y1 y3) y2)))) -> Peano.lt (@nsum a0 y0 y1) (Nat.mul (@CARD a0 y0) y2).
Definition term105 (a0 : Type') (x0 : nat) := forall y0 : a0 -> nat, forall y1 : a0 -> Prop, forall y2 : a0, (@FINITE a0 y1) -> (forall y3 : a0, (@IN a0 y3 y1) -> Peano.le (y0 y3) x0) -> (@IN a0 y2 y1) -> (Peano.lt (y0 y2) x0) -> exists y3 : a0, (@IN a0 y3 y1) /\ (Peano.lt (y0 y3) x0).
Definition term104 (a0 : Type') (x0 : nat) := forall y0 : a0 -> nat, forall y1 : a0 -> Prop, forall y2 : a0, (@FINITE a0 y1) -> (forall y3 : a0, (@IN a0 y3 y1) -> Peano.le (y0 y3) x0) -> (@IN a0 y2 y1) -> (Peano.lt (y0 y2) x0) -> (~ (exists y3 : a0, (@IN a0 y3 y1) /\ (Peano.lt (y0 y3) x0))) -> False.
Definition term12 (a0 : Type') := forall y0 : a0 -> nat, forall y1 : a0 -> Prop, forall y2 : a0 -> nat, ((@FINITE a0 y1) /\ ((forall y3 : a0, (@IN a0 y3 y1) -> Peano.le (y0 y3) (y2 y3)) /\ (exists y3 : a0, (@IN a0 y3 y1) /\ (Peano.lt (y0 y3) (y2 y3))))) -> Peano.lt (@nsum a0 y1 y0) (@nsum a0 y1 y2).
Definition term0 (a0 : Type') := forall y0 : a0 -> nat, forall y1 : a0 -> nat, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ ((forall y3 : a0, (@IN a0 y3 y2) -> Peano.le (y0 y3) (y1 y3)) /\ (exists y3 : a0, (@IN a0 y3 y2) /\ (Peano.lt (y0 y3) (y1 y3))))) -> Peano.lt (@nsum a0 y2 y0) (@nsum a0 y2 y1).
Definition term87 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) (x3 : nat) := (@IN a0 x0 x1) -> (Peano.lt (x2 x0) x3) -> (~ (exists y0 : a0, (@IN a0 y0 x1) /\ (Peano.lt (x2 y0) x3))) -> False.
Definition term75 (x0 : Prop) := (~ x0) -> False.
Definition term49 (a0 : Type') (x0 : nat) (x1 : a0) := (fun y0 : a0 => (fun y1 : a0 => x0) y0) x1.
Definition term112 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : nat) := (~ (@IN a0 x2 x0)) \/ (~ (Peano.lt (x1 x2) x3)).
Definition term62 (a0 : Type') := forall y0 : a0, True.
Definition term14 (a0 : Type') (x0 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : a0 -> Prop, forall y2 : a0 -> nat, ((@FINITE a0 y1) /\ ((forall y3 : a0, (@IN a0 y3 y1) -> Peano.le (y0 y3) (y2 y3)) /\ (exists y3 : a0, (@IN a0 y3 y1) /\ (Peano.lt (y0 y3) (y2 y3))))) -> Peano.lt (@nsum a0 y1 y0) (@nsum a0 y1 y2)) x0.
Definition term1 (a0 : Type') (x0 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : a0 -> nat, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ ((forall y3 : a0, (@IN a0 y3 y2) -> Peano.le (y0 y3) (y1 y3)) /\ (exists y3 : a0, (@IN a0 y3 y2) /\ (Peano.lt (y0 y3) (y1 y3))))) -> Peano.lt (@nsum a0 y2 y0) (@nsum a0 y2 y1)) x0.
Definition term16 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := (fun y0 : a0 -> nat => ((@FINITE a0 x1) /\ ((forall y1 : a0, (@IN a0 y1 x1) -> Peano.le (x0 y1) (y0 y1)) /\ (exists y1 : a0, (@IN a0 y1 x1) /\ (Peano.lt (x0 y1) (y0 y1))))) -> Peano.lt (@nsum a0 x1 x0) (@nsum a0 x1 y0)) x2.
Definition term5 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ ((forall y1 : a0, (@IN a0 y1 y0) -> Peano.le (x0 y1) (x1 y1)) /\ (exists y1 : a0, (@IN a0 y1 y0) /\ (Peano.lt (x0 y1) (x1 y1))))) -> Peano.lt (@nsum a0 y0 x0) (@nsum a0 y0 x1)) x2.
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) ((fun y1 : a0 => x2) y0).
Definition term64 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := and (forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) ((fun y1 : a0 => x2) y0)).
Definition term29 (x0 : nat) := forall y0 : nat, (exists y1 : nat, (Peano.lt x0 y1) /\ (Peano.le y1 y0)) -> Peano.lt x0 y0.
Definition term13 (a0 : Type') := (forall y0 : a0 -> nat, forall y1 : a0 -> nat, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ ((forall y3 : a0, (@IN a0 y3 y2) -> Peano.le (y0 y3) (y1 y3)) /\ (exists y3 : a0, (@IN a0 y3 y2) /\ (Peano.lt (y0 y3) (y1 y3))))) -> Peano.lt (@nsum a0 y2 y0) (@nsum a0 y2 y1)) -> forall y0 : a0 -> nat, forall y1 : a0 -> Prop, forall y2 : a0 -> nat, ((@FINITE a0 y1) /\ ((forall y3 : a0, (@IN a0 y3 y1) -> Peano.le (y0 y3) (y2 y3)) /\ (exists y3 : a0, (@IN a0 y3 y1) /\ (Peano.lt (y0 y3) (y2 y3))))) -> Peano.lt (@nsum a0 y1 y0) (@nsum a0 y1 y2).
Definition term123 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (@IN a0 x0 x1).
Definition term127 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term93 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) (x3 : nat) := (@FINITE a0 x1) -> (forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x2 y0) x3) -> (@IN a0 x0 x1) -> (Peano.lt (x2 x0) x3) -> exists y0 : a0, (@IN a0 y0 x1) /\ (Peano.lt (x2 y0) x3).
Definition term78 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) (x3 : nat) := (@FINITE a0 x1) -> (forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x2 y0) x3) -> (@IN a0 x0 x1) -> (Peano.lt (x2 x0) x3) -> (~ (exists y0 : a0, (@IN a0 y0 x1) /\ (Peano.lt (x2 y0) x3))) -> False.
Definition term124 (x0 : Prop) := (~ x0) -> x0.
Definition term52 (a0 : Type') (x0 : nat) (x1 : a0) := @eq nat ((fun y0 : a0 => (fun y1 : a0 => x0) y0) x1).
Definition term80 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) (x3 : nat) := (((@FINITE a0 x1) -> (forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x2 y0) x3) -> (@IN a0 x0 x1) -> (Peano.lt (x2 x0) x3) -> (~ (exists y0 : a0, (@IN a0 y0 x1) /\ (Peano.lt (x2 y0) x3))) -> False) -> (@FINITE a0 x1) -> (forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x2 y0) x3) -> (@IN a0 x0 x1) -> (Peano.lt (x2 x0) x3) -> (~ (exists y0 : a0, (@IN a0 y0 x1) /\ (Peano.lt (x2 y0) x3))) -> False) -> (@FINITE a0 x1) -> (forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x2 y0) x3) -> (@IN a0 x0 x1) -> (Peano.lt (x2 x0) x3) -> (~ (exists y0 : a0, (@IN a0 y0 x1) /\ (Peano.lt (x2 y0) x3))) -> False.
Definition term58 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) (x3 : a0) := (@IN a0 x3 x0) -> Peano.le (x1 x3) ((fun y0 : a0 => x2) x3).
Definition term39 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) (x2 : nat) := Peano.lt (x0 x1) x2.
Definition term76 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := (~ (exists y0 : a0, (@IN a0 y0 x0) /\ (Peano.lt (x1 y0) x2))) -> False.
Definition term128 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term121 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) (x3 : a0) := (fun y0 : a0 => (~ (@IN a0 y0 x0)) \/ (~ (Peano.lt (x1 y0) x2))) x3.
Definition term146 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : nat) := (Peano.lt (@nsum a0 x1 x0) (@nsum a0 x1 (fun y0 : a0 => x2))) /\ (Peano.le (@nsum a0 x1 (fun y0 : a0 => x2)) (Nat.mul (@CARD a0 x1) x2)).
Definition term54 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := Peano.le (x0 x1).
Definition term138 (a0 : Type') (x0 : nat) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@nsum a0 y0 (fun y1 : a0 => x0)) = (Nat.mul (@CARD a0 y0) x0).
Definition term20 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.le y0 y1)) -> Peano.lt x0 y1) x1.
Definition term15 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> nat, ((@FINITE a0 y0) /\ ((forall y2 : a0, (@IN a0 y2 y0) -> Peano.le (x0 y2) (y1 y2)) /\ (exists y2 : a0, (@IN a0 y2 y0) /\ (Peano.lt (x0 y2) (y1 y2))))) -> Peano.lt (@nsum a0 y0 x0) (@nsum a0 y0 y1)) x1.
Definition term3 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((forall y2 : a0, (@IN a0 y2 y1) -> Peano.le (x0 y2) (y0 y2)) /\ (exists y2 : a0, (@IN a0 y2 y1) /\ (Peano.lt (x0 y2) (y0 y2))))) -> Peano.lt (@nsum a0 y1 x0) (@nsum a0 y1 y0)) x1.
Definition term110 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := fun y0 : a0 => (@IN a0 y0 x0) -> Peano.le (x1 y0) x2.
Definition term107 (a0 : Type') := fun y0 : nat => forall y1 : a0 -> nat, forall y2 : a0 -> Prop, forall y3 : a0, (@FINITE a0 y2) -> (forall y4 : a0, (@IN a0 y4 y2) -> Peano.le (y1 y4) y0) -> (@IN a0 y3 y2) -> (Peano.lt (y1 y3) y0) -> exists y4 : a0, (@IN a0 y4 y2) /\ (Peano.lt (y1 y4) y0).
Definition term106 (a0 : Type') := fun y0 : nat => forall y1 : a0 -> nat, forall y2 : a0 -> Prop, forall y3 : a0, (@FINITE a0 y2) -> (forall y4 : a0, (@IN a0 y4 y2) -> Peano.le (y1 y4) y0) -> (@IN a0 y3 y2) -> (Peano.lt (y1 y3) y0) -> (~ (exists y4 : a0, (@IN a0 y4 y2) /\ (Peano.lt (y1 y4) y0))) -> False.
Definition term118 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := fun y0 : a0 => ~ ((fun y1 : a0 => (@IN a0 y1 x0) /\ (Peano.lt (x1 y1) x2)) y0).
Definition term119 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := fun y0 : a0 => (~ (@IN a0 y0 x0)) \/ (~ (Peano.lt (x1 y0) x2)).
Definition term46 (a0 : Type') (x0 : a0 -> Prop) := and (@FINITE a0 x0).
Definition term73 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := True /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (Peano.lt (x1 y0) x2)).
Definition term136 (x0 : nat) := (fun y0 : nat => Peano.le y0 y0) x0.
Definition term139 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@nsum a0 y0 (fun y1 : a0 => x0)) = (Nat.mul (@CARD a0 y0) x0)) x1.
Definition term67 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@IN a0 x0 x1).
Definition term8 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := Peano.lt (@nsum a0 x1 x0) (@nsum a0 x1 x2).
Definition term45 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : nat) := (@IN a0 x2 x0) -> Peano.le (x1 x2) x3.
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Peano.lt x1 x0) /\ (Peano.le x0 y0)) -> Peano.lt x1 y0) x2.
Definition term68 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) (x3 : a0) := (@IN a0 x3 x0) /\ (Peano.lt (x1 x3) ((fun y0 : a0 => x2) x3)).
Definition term129 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : nat) := ((@IN a0 x2 x0) /\ (Peano.lt (x1 x2) x3)) -> False.
Definition term95 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := fun y0 : a0 => (@FINITE a0 x0) -> (forall y1 : a0, (@IN a0 y1 x0) -> Peano.le (x1 y1) x2) -> (@IN a0 y0 x0) -> (Peano.lt (x1 y0) x2) -> exists y1 : a0, (@IN a0 y1 x0) /\ (Peano.lt (x1 y1) x2).
Definition term94 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := fun y0 : a0 => (@FINITE a0 x0) -> (forall y1 : a0, (@IN a0 y1 x0) -> Peano.le (x1 y1) x2) -> (@IN a0 y0 x0) -> (Peano.lt (x1 y0) x2) -> (~ (exists y1 : a0, (@IN a0 y1 x0) /\ (Peano.lt (x1 y1) x2))) -> False.
Definition term28 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Peano.lt x0 y0) /\ (Peano.le y0 x1)) -> Peano.lt x0 x1.
Definition term148 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : nat) := fun y0 : nat => (Peano.lt (@nsum a0 x1 x0) y0) /\ (Peano.le y0 (Nat.mul (@CARD a0 x1) x2)).
Definition term132 (a0 : Type') (x0 : nat) (x1 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : a0 -> Prop, forall y2 : a0, (@FINITE a0 y1) -> (forall y3 : a0, (@IN a0 y3 y1) -> Peano.le (y0 y3) x0) -> (@IN a0 y2 y1) -> (Peano.lt (y0 y2) x0) -> (~ (exists y3 : a0, (@IN a0 y3 y1) /\ (Peano.lt (y0 y3) x0))) -> False) x1.
Definition term97 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := forall y0 : a0, (@FINITE a0 x0) -> (forall y1 : a0, (@IN a0 y1 x0) -> Peano.le (x1 y1) x2) -> (@IN a0 y0 x0) -> (Peano.lt (x1 y0) x2) -> exists y1 : a0, (@IN a0 y1 x0) /\ (Peano.lt (x1 y1) x2).
Definition term96 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := forall y0 : a0, (@FINITE a0 x0) -> (forall y1 : a0, (@IN a0 y1 x0) -> Peano.le (x1 y1) x2) -> (@IN a0 y0 x0) -> (Peano.lt (x1 y0) x2) -> (~ (exists y1 : a0, (@IN a0 y1 x0) /\ (Peano.lt (x1 y1) x2))) -> False.
Definition term133 (a0 : Type') (x0 : a0 -> nat) (x1 : nat) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (@FINITE a0 y0) -> (forall y2 : a0, (@IN a0 y2 y0) -> Peano.le (x0 y2) x1) -> (@IN a0 y1 y0) -> (Peano.lt (x0 y1) x1) -> (~ (exists y2 : a0, (@IN a0 y2 y0) /\ (Peano.lt (x0 y2) x1))) -> False) x2.
Definition term114 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term44 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) (x3 : a0) := (fun y0 : a0 => (@IN a0 y0 x0) -> Peano.le (x1 y0) x2) x3.
Definition term47 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term40 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : nat) := (exists y0 : nat, (Peano.lt (@nsum a0 x1 x0) y0) /\ (Peano.le y0 (Nat.mul (@CARD a0 x1) x2))) -> Peano.lt (@nsum a0 x1 x0) (Nat.mul (@CARD a0 x1) x2).
Definition term53 (a0 : Type') (x0 : nat) (x1 : a0) := @eq nat ((fun y0 : a0 => x0) x1).
Definition term99 (a0 : Type') (x0 : a0 -> nat) (x1 : nat) := fun y0 : a0 -> Prop => forall y1 : a0, (@FINITE a0 y0) -> (forall y2 : a0, (@IN a0 y2 y0) -> Peano.le (x0 y2) x1) -> (@IN a0 y1 y0) -> (Peano.lt (x0 y1) x1) -> exists y2 : a0, (@IN a0 y2 y0) /\ (Peano.lt (x0 y2) x1).
Definition term98 (a0 : Type') (x0 : a0 -> nat) (x1 : nat) := fun y0 : a0 -> Prop => forall y1 : a0, (@FINITE a0 y0) -> (forall y2 : a0, (@IN a0 y2 y0) -> Peano.le (x0 y2) x1) -> (@IN a0 y1 y0) -> (Peano.lt (x0 y1) x1) -> (~ (exists y2 : a0, (@IN a0 y2 y0) /\ (Peano.lt (x0 y2) x1))) -> False.
Definition term90 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) (x3 : nat) := (forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x2 y0) x3) -> (@IN a0 x0 x1) -> (Peano.lt (x2 x0) x3) -> (~ (exists y0 : a0, (@IN a0 y0 x1) /\ (Peano.lt (x2 y0) x3))) -> False.
Definition term50 (a0 : Type') (x0 : nat) (x1 : a0) := (fun y0 : a0 => x0) x1.
Definition term109 (a0 : Type') := forall y0 : nat, forall y1 : a0 -> nat, forall y2 : a0 -> Prop, forall y3 : a0, (@FINITE a0 y2) -> (forall y4 : a0, (@IN a0 y4 y2) -> Peano.le (y1 y4) y0) -> (@IN a0 y3 y2) -> (Peano.lt (y1 y3) y0) -> exists y4 : a0, (@IN a0 y4 y2) /\ (Peano.lt (y1 y4) y0).
Definition term108 (a0 : Type') := forall y0 : nat, forall y1 : a0 -> nat, forall y2 : a0 -> Prop, forall y3 : a0, (@FINITE a0 y2) -> (forall y4 : a0, (@IN a0 y4 y2) -> Peano.le (y1 y4) y0) -> (@IN a0 y3 y2) -> (Peano.lt (y1 y3) y0) -> (~ (exists y4 : a0, (@IN a0 y4 y2) /\ (Peano.lt (y1 y4) y0))) -> False.
Definition term30 := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (Peano.lt y0 y2) /\ (Peano.le y2 y1)) -> Peano.lt y0 y1.
Definition term19 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.le y0 y1)) -> Peano.lt x0 y1.
Definition term17 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2.
Definition term60 (a0 : Type') := fun y0 : a0 => True.
Definition term48 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term85 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) (x3 : nat) := (Peano.lt (x2 x0) x3) -> (~ (exists y0 : a0, (@IN a0 y0 x1) /\ (Peano.lt (x2 y0) x3))) -> False.
Definition term77 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := ~ (exists y0 : a0, (@IN a0 y0 x0) /\ (Peano.lt (x1 y0) x2)).
Definition term111 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : nat) := ~ ((@IN a0 x2 x0) /\ (Peano.lt (x1 x2) x3)).
Definition term147 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : nat) := exists y0 : nat, (Peano.lt (@nsum a0 x1 x0) y0) /\ (Peano.le y0 (Nat.mul (@CARD a0 x1) x2)).
Definition term59 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := fun y0 : a0 => (@IN a0 y0 x0) -> Peano.le (x1 y0) ((fun y1 : a0 => x2) y0).
Definition term143 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := Peano.le (Nat.mul (@CARD a0 x0) x1).
Definition term72 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := (forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) ((fun y1 : a0 => x2) y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (Peano.lt (x1 y0) ((fun y1 : a0 => x2) y0))).
Definition term69 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := fun y0 : a0 => (@IN a0 y0 x0) /\ (Peano.lt (x1 y0) ((fun y1 : a0 => x2) y0)).
Definition term84 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) (x2 : nat) := imp (Peano.lt (x0 x1) x2).
Definition term142 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := Peano.le (@nsum a0 x0 (fun y0 : a0 => x1)).
Definition term135 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : nat) := Peano.lt (@nsum a0 x1 x0) (@nsum a0 x1 (fun y0 : a0 => x2)).
Definition term38 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0) (x3 : nat) := (@IN a0 x2 x0) /\ (Peano.lt (x1 x2) x3).
Definition term131 (a0 : Type') (x0 : nat) := (fun y0 : nat => forall y1 : a0 -> nat, forall y2 : a0 -> Prop, forall y3 : a0, (@FINITE a0 y2) -> (forall y4 : a0, (@IN a0 y4 y2) -> Peano.le (y1 y4) y0) -> (@IN a0 y3 y2) -> (Peano.lt (y1 y3) y0) -> (~ (exists y4 : a0, (@IN a0 y4 y2) /\ (Peano.lt (y1 y4) y0))) -> False) x0.
Definition term122 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ (@IN a0 x0 x1)) -> @IN a0 x0 x1.
Definition term140 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) -> (@nsum a0 x0 (fun y0 : a0 => x1)) = (Nat.mul (@CARD a0 x0) x1).
Definition term71 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := exists y0 : a0, (@IN a0 y0 x0) /\ (Peano.lt (x1 y0) ((fun y1 : a0 => x2) y0)).
Definition term150 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : nat) := ((@FINITE a0 x1) /\ ((forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x0 y0) x2) /\ (exists y0 : a0, (@IN a0 y0 x1) /\ (Peano.lt (x0 y0) x2)))) -> Peano.lt (@nsum a0 x1 x0) (Nat.mul (@CARD a0 x1) x2).
Definition term42 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : nat) := ((@FINITE a0 x1) /\ ((forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x0 y0) ((fun y1 : a0 => x2) y0)) /\ (exists y0 : a0, (@IN a0 y0 x1) /\ (Peano.lt (x0 y0) ((fun y1 : a0 => x2) y0))))) -> Peano.lt (@nsum a0 x1 x0) (@nsum a0 x1 (fun y0 : a0 => x2)).
Definition term117 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) (x3 : a0) := ~ ((fun y0 : a0 => (@IN a0 y0 x0) /\ (Peano.lt (x1 y0) x2)) x3).
Definition term81 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) (x3 : nat) := (((@FINITE a0 x1) -> (forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x2 y0) x3) -> (@IN a0 x0 x1) -> (Peano.lt (x2 x0) x3) -> (~ (exists y0 : a0, (@IN a0 y0 x1) /\ (Peano.lt (x2 y0) x3))) -> False) -> (@FINITE a0 x1) -> (forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x2 y0) x3) -> (@IN a0 x0 x1) -> (Peano.lt (x2 x0) x3) -> (~ (exists y0 : a0, (@IN a0 y0 x1) /\ (Peano.lt (x2 y0) x3))) -> False) -> ((@FINITE a0 x1) -> (forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x2 y0) x3) -> (@IN a0 x0 x1) -> (Peano.lt (x2 x0) x3) -> (~ (exists y0 : a0, (@IN a0 y0 x1) /\ (Peano.lt (x2 y0) x3))) -> False) -> (@FINITE a0 x1) -> (forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x2 y0) x3) -> (@IN a0 x0 x1) -> (Peano.lt (x2 x0) x3) -> (~ (exists y0 : a0, (@IN a0 y0 x1) /\ (Peano.lt (x2 y0) x3))) -> False.
Definition term125 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) (x2 : nat) := (~ (Peano.lt (x0 x1) x2)) -> Peano.lt (x0 x1) x2.
Definition term89 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := imp (forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) x2).
Definition term9 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := (forall y0 : a0 -> nat, forall y1 : a0 -> nat, forall y2 : a0 -> Prop, ((@FINITE a0 y2) /\ ((forall y3 : a0, (@IN a0 y3 y2) -> Peano.le (y0 y3) (y1 y3)) /\ (exists y3 : a0, (@IN a0 y3 y2) /\ (Peano.lt (y0 y3) (y1 y3))))) -> Peano.lt (@nsum a0 y2 y0) (@nsum a0 y2 y1)) -> Peano.lt (@nsum a0 x1 x0) (@nsum a0 x1 x2).
Definition term57 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term41 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := Nat.mul (@CARD a0 x0) x1.
Definition term21 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.lt x1 x0) /\ (Peano.le x0 y0)) -> Peano.lt x1 y0.
Definition term120 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := forall y0 : a0, (~ (@IN a0 y0 x0)) \/ (~ (Peano.lt (x1 y0) x2)).
Definition term152 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> nat, forall y1 : nat, ((@FINITE a0 x0) /\ ((forall y2 : a0, (@IN a0 y2 x0) -> Peano.le (y0 y2) y1) /\ (exists y2 : a0, (@IN a0 y2 x0) /\ (Peano.lt (y0 y2) y1)))) -> Peano.lt (@nsum a0 x0 y0) (Nat.mul (@CARD a0 x0) y1).
Definition term11 (a0 : Type') (x0 : a0 -> nat) := forall y0 : a0 -> Prop, forall y1 : a0 -> nat, ((@FINITE a0 y0) /\ ((forall y2 : a0, (@IN a0 y2 y0) -> Peano.le (x0 y2) (y1 y2)) /\ (exists y2 : a0, (@IN a0 y2 y0) /\ (Peano.lt (x0 y2) (y1 y2))))) -> Peano.lt (@nsum a0 y0 x0) (@nsum a0 y0 y1).
Definition term2 (a0 : Type') (x0 : a0 -> nat) := forall y0 : a0 -> nat, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ ((forall y2 : a0, (@IN a0 y2 y1) -> Peano.le (x0 y2) (y0 y2)) /\ (exists y2 : a0, (@IN a0 y2 y1) /\ (Peano.lt (x0 y2) (y0 y2))))) -> Peano.lt (@nsum a0 y1 x0) (@nsum a0 y1 y0).
Definition term91 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) (x3 : nat) := (forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x2 y0) x3) -> (@IN a0 x0 x1) -> (Peano.lt (x2 x0) x3) -> exists y0 : a0, (@IN a0 y0 x1) /\ (Peano.lt (x2 y0) x3).
Definition term74 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := (@FINITE a0 x0) /\ ((forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) ((fun y1 : a0 => x2) y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (Peano.lt (x1 y0) ((fun y1 : a0 => x2) y0)))).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := (@FINITE a0 x0) /\ ((forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) x2) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (Peano.lt (x1 y0) x2))).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : a0 -> nat) := (@FINITE a0 x0) /\ ((forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) (x2 y0)) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (Peano.lt (x1 y0) (x2 y0)))).
Definition term25 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt y0 y1) /\ (Peano.le y1 y2)) -> Peano.lt y0 y2) -> Peano.lt x0 x1.
Definition term86 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) (x3 : nat) := (Peano.lt (x2 x0) x3) -> exists y0 : a0, (@IN a0 y0 x1) /\ (Peano.lt (x2 y0) x3).
Definition term116 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) (x3 : a0) := (fun y0 : a0 => (@IN a0 y0 x0) /\ (Peano.lt (x1 y0) x2)) x3.
Definition term65 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := Peano.lt (x0 x1).
Definition term32 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (Peano.lt y0 y2) /\ (Peano.le y2 y1)) -> Peano.lt y0 y1) x0.
Definition term79 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) (x3 : nat) := ((@FINITE a0 x1) -> (forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x2 y0) x3) -> (@IN a0 x0 x1) -> (Peano.lt (x2 x0) x3) -> (~ (exists y0 : a0, (@IN a0 y0 x1) /\ (Peano.lt (x2 y0) x3))) -> False) -> (@FINITE a0 x1) -> (forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x2 y0) x3) -> (@IN a0 x0 x1) -> (Peano.lt (x2 x0) x3) -> (~ (exists y0 : a0, (@IN a0 y0 x1) /\ (Peano.lt (x2 y0) x3))) -> False.
Definition term151 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) := forall y0 : nat, ((@FINITE a0 x1) /\ ((forall y1 : a0, (@IN a0 y1 x1) -> Peano.le (x0 y1) y0) /\ (exists y1 : a0, (@IN a0 y1 x1) /\ (Peano.lt (x0 y1) y0)))) -> Peano.lt (@nsum a0 x1 x0) (Nat.mul (@CARD a0 x1) y0).
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.lt x1 x0) /\ (Peano.le x0 x2)) -> Peano.lt x1 x2.
Definition term51 (a0 : Type') (x0 : nat) := fun y0 : a0 => (fun y1 : a0 => x0) y0.
Definition term56 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) (x2 : nat) := Peano.le (x0 x1) x2.
Definition term145 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := Peano.le (Nat.mul (@CARD a0 x0) x1) (Nat.mul (@CARD a0 x0) x1).
Definition term55 (a0 : Type') (x0 : a0 -> nat) (x1 : nat) (x2 : a0) := Peano.le (x0 x2) ((fun y0 : a0 => x1) x2).
Definition term141 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @nsum a0 x0 (fun y0 : a0 => x1).
Definition term149 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : nat) := Peano.lt (@nsum a0 x1 x0) (Nat.mul (@CARD a0 x1) x2).
Definition term27 (x0 : nat) (x1 : nat) := fun y0 : nat => (Peano.lt x0 y0) /\ (Peano.le y0 x1).
Definition term134 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) (x3 : a0) := (fun y0 : a0 => (@FINITE a0 x0) -> (forall y1 : a0, (@IN a0 y1 x0) -> Peano.le (x1 y1) x2) -> (@IN a0 y0 x0) -> (Peano.lt (x1 y0) x2) -> (~ (exists y1 : a0, (@IN a0 y1 x0) /\ (Peano.lt (x1 y1) x2))) -> False) x3.
Definition term6 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) (x2 : a0 -> nat) := ((@FINITE a0 x1) /\ ((forall y0 : a0, (@IN a0 y0 x1) -> Peano.le (x0 y0) (x2 y0)) /\ (exists y0 : a0, (@IN a0 y0 x1) /\ (Peano.lt (x0 y0) (x2 y0))))) -> Peano.lt (@nsum a0 x1 x0) (@nsum a0 x1 x2).
Definition term144 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := Peano.le (@nsum a0 x0 (fun y0 : a0 => x1)) (Nat.mul (@CARD a0 x0) x1).
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := (forall y0 : a0, (@IN a0 y0 x0) -> Peano.le (x1 y0) x2) /\ (exists y0 : a0, (@IN a0 y0 x0) /\ (Peano.lt (x1 y0) x2)).
Definition term10 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) := forall y0 : a0 -> nat, ((@FINITE a0 x1) /\ ((forall y1 : a0, (@IN a0 y1 x1) -> Peano.le (x0 y1) (y0 y1)) /\ (exists y1 : a0, (@IN a0 y1 x1) /\ (Peano.lt (x0 y1) (y0 y1))))) -> Peano.lt (@nsum a0 x1 x0) (@nsum a0 x1 y0).
Definition term4 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> nat) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ ((forall y1 : a0, (@IN a0 y1 y0) -> Peano.le (x0 y1) (x1 y1)) /\ (exists y1 : a0, (@IN a0 y1 y0) /\ (Peano.lt (x0 y1) (x1 y1))))) -> Peano.lt (@nsum a0 y0 x0) (@nsum a0 y0 x1).
Definition term66 (a0 : Type') (x0 : a0 -> nat) (x1 : nat) (x2 : a0) := Peano.lt (x0 x2) ((fun y0 : a0 => x1) x2).
Definition term103 (a0 : Type') (x0 : nat) := fun y0 : a0 -> nat => forall y1 : a0 -> Prop, forall y2 : a0, (@FINITE a0 y1) -> (forall y3 : a0, (@IN a0 y3 y1) -> Peano.le (y0 y3) x0) -> (@IN a0 y2 y1) -> (Peano.lt (y0 y2) x0) -> exists y3 : a0, (@IN a0 y3 y1) /\ (Peano.lt (y0 y3) x0).
Definition term102 (a0 : Type') (x0 : nat) := fun y0 : a0 -> nat => forall y1 : a0 -> Prop, forall y2 : a0, (@FINITE a0 y1) -> (forall y3 : a0, (@IN a0 y3 y1) -> Peano.le (y0 y3) x0) -> (@IN a0 y2 y1) -> (Peano.lt (y0 y2) x0) -> (~ (exists y3 : a0, (@IN a0 y3 y1) /\ (Peano.lt (y0 y3) x0))) -> False.
Definition term82 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := ~ (~ (exists y0 : a0, (@IN a0 y0 x0) /\ (Peano.lt (x1 y0) x2))).
Definition term115 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := forall y0 : a0, ~ ((fun y1 : a0 => (@IN a0 y1 x0) /\ (Peano.lt (x1 y1) x2)) y0).
Definition term101 (a0 : Type') (x0 : a0 -> nat) (x1 : nat) := forall y0 : a0 -> Prop, forall y1 : a0, (@FINITE a0 y0) -> (forall y2 : a0, (@IN a0 y2 y0) -> Peano.le (x0 y2) x1) -> (@IN a0 y1 y0) -> (Peano.lt (x0 y1) x1) -> exists y2 : a0, (@IN a0 y2 y0) /\ (Peano.lt (x0 y2) x1).
Definition term100 (a0 : Type') (x0 : a0 -> nat) (x1 : nat) := forall y0 : a0 -> Prop, forall y1 : a0, (@FINITE a0 y0) -> (forall y2 : a0, (@IN a0 y2 y0) -> Peano.le (x0 y2) x1) -> (@IN a0 y1 y0) -> (Peano.lt (x0 y1) x1) -> (~ (exists y2 : a0, (@IN a0 y2 y0) /\ (Peano.lt (x0 y2) x1))) -> False.
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := exists y0 : a0, (@IN a0 y0 x0) /\ (Peano.lt (x1 y0) x2).
Definition term70 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) (x2 : nat) := fun y0 : a0 => (@IN a0 y0 x0) /\ (Peano.lt (x1 y0) x2).
Definition term33 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (Peano.lt x0 y1) /\ (Peano.le y1 y0)) -> Peano.lt x0 y0) x1.
