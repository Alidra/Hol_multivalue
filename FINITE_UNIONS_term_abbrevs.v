Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term16 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@SUBSET a0 y0 x0) -> (@FINITE a0 x0) -> @FINITE a0 y0.
Definition term7 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@SUBSET a0 x0 y0) -> (@FINITE a0 y0) -> @FINITE a0 x0.
Definition term154 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => (~ (forall y1 : a0 -> Prop, (y0 y1) -> forall y2 : a0, (y1 y2) -> exists y3 : a0 -> Prop, (y0 y3) /\ (y3 y2))) -> False) x0.
Definition term8 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0.
Definition term128 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, ~ (x0 y0).
Definition term153 := (~ False) -> False.
Definition term66 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := exists y0 : a0 -> Prop, @SETSPEC (a0 -> Prop) x0 (forall y1 : a0, (@IN a0 y1 y0) -> @IN a0 y1 (@UNIONS a0 x1)) y0.
Definition term1 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> x1 -> x2.
Definition term59 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : type686 a0) := @SETSPEC (a0 -> Prop) x0 (@SUBSET a0 x1 (@UNIONS a0 x2)).
Definition term27 (a0 : Type') (x0 : type686 a0) := (fun y0 : Prop => y0 \/ (~ y0)) (@FINITE (a0 -> Prop) x0).
Definition term43 (a0 : Type') (x0 : type686 a0) := @FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 (@UNIONS a0 x0)) y1)).
Definition term152 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (@I ((a0 -> Prop) -> Prop) x0 x1) /\ (@I (a0 -> Prop) x1 x2).
Definition term118 (x0 : Prop) := ~ (~ x0).
Definition term37 (a0 : Type') (x0 : type686 a0) := (@FINITE (a0 -> Prop) x0) /\ (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> @FINITE a0 y0).
Definition term95 (a0 : Type') (x0 : type686 a0) (x1 : a0) := exists y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) /\ (@IN a0 x1 y0).
Definition term140 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := or (~ (@I ((a0 -> Prop) -> Prop) x0 x1)).
Definition term120 (a0 : Type') := fun y0 : type686 a0 => forall y1 : a0 -> Prop, (y0 y1) -> forall y2 : a0, (y1 y2) -> exists y3 : a0 -> Prop, (y0 y3) /\ (y3 y2).
Definition term113 (a0 : Type') (x0 : type686 a0) := ~ (forall y0 : a0 -> Prop, (x0 y0) -> forall y1 : a0, (y0 y1) -> exists y2 : a0 -> Prop, (x0 y2) /\ (y2 y1)).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> @FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 y0) y2))) x0.
Definition term135 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term28 (a0 : Type') (x0 : type686 a0) := (@FINITE (a0 -> Prop) x0) \/ (~ (@FINITE (a0 -> Prop) x0)).
Definition term94 (a0 : Type') (x0 : a0) (x1 : type686 a0) := @IN a0 x0 (@UNIONS a0 x1).
Definition term22 (x0 : Prop) := forall y0 : Prop, ((~ x0) -> ~ y0) = (y0 -> x0).
Definition term131 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := ~ ((fun y0 : a0 -> Prop => (x0 y0) /\ (y0 x1)) x2).
Definition term82 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (@IN a0 y1 y0) -> @IN a0 y1 (@UNIONS a0 x0)) x1.
Definition term111 (x0 : Prop) := (~ x0) -> False.
Definition term103 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : type686 a0) := (@IN a0 x1 x0) -> @IN a0 x1 (@UNIONS a0 x2).
Definition term63 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := fun y0 : a0 -> Prop => @SETSPEC (a0 -> Prop) x0 (@SUBSET a0 y0 (@UNIONS a0 x1)) y0.
Definition term88 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => forall y3 : a0, (@IN a0 y3 y2) -> @IN a0 y3 (@UNIONS a0 x0)) y1) y1.
Definition term68 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (forall y2 : a0, (@IN a0 y2 y1) -> @IN a0 y2 (@UNIONS a0 x0)) y1.
Definition term67 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 (@UNIONS a0 x0)) y1.
Definition term62 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 (forall y0 : a0, (@IN a0 y0 x2) -> @IN a0 y0 (@UNIONS a0 x1)) x2.
Definition term74 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := (@IN (a0 -> Prop) x0 x1) -> @IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (forall y2 : a0, (@IN a0 y2 y1) -> @IN a0 y2 (@UNIONS a0 x1)) y1)).
Definition term73 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := (@IN (a0 -> Prop) x0 x1) -> @IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 (@UNIONS a0 x1)) y1)).
Definition term155 (a0 : Type') (x0 : type686 a0) := (@FINITE a0 (@UNIONS a0 x0)) -> False.
Definition term54 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> @IN (a0 -> Prop) y0 x1.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x0) /\ (@SUBSET a0 x1 x0)) -> @FINITE a0 x1.
Definition term77 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> @IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (forall y3 : a0, (@IN a0 y3 y2) -> @IN a0 y3 (@UNIONS a0 x0)) y2)).
Definition term56 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> @IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 (@UNIONS a0 x0)) y2)).
Definition term48 (a0 : Type') (x0 : type686 a0) := (~ (@FINITE (a0 -> Prop) x0)) -> ~ (@FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 (@UNIONS a0 x0)) y1))).
Definition term98 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := (@IN (a0 -> Prop) x2 x0) /\ (@IN a0 x1 x2).
Definition term26 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> @FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x0) y1)).
Definition term18 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (@SUBSET a0 y0 y1) -> (@FINITE a0 y1) -> @FINITE a0 y0) -> forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (@SUBSET a0 y1 y0) -> (@FINITE a0 y0) -> @FINITE a0 y1.
Definition term147 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (@I (a0 -> Prop) x0 x1)) -> @I (a0 -> Prop) x0 x1.
Definition term31 (a0 : Type') (x0 : type686 a0) := (@FINITE (a0 -> Prop) x0) -> (@FINITE a0 (@UNIONS a0 x0)) = (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> @FINITE a0 y0).
Definition term100 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) /\ (@IN a0 x1 y0).
Definition term148 (x0 : Prop) (x1 : Prop) := (~ x0) \/ (~ x1).
Definition term146 (x0 : Prop) := (~ x0) -> x0.
Definition term78 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := imp (x0 x1).
Definition term126 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x1)) \/ (~ (x1 x2)).
Definition term133 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => (~ (x0 y0)) \/ (~ (y0 x1)).
Definition term9 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@SUBSET a0 y0 y1) -> (@FINITE a0 y1) -> @FINITE a0 y0.
Definition term123 (a0 : Type') (x0 : type686 a0) (x1 : a0) := (~ (exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x1))) -> False.
Definition term21 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((~ y0) -> ~ y1) = (y1 -> y0)) x0.
Definition term149 (x0 : Prop) (x1 : Prop) := ~ (x0 /\ x1).
Definition term44 (a0 : Type') (x0 : type686 a0) := (@FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 (@UNIONS a0 x0)) y1))) -> False.
Definition term134 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, (~ (x0 y0)) \/ (~ (y0 x1)).
Definition term34 (a0 : Type') (x0 : type686 a0) := @eq Prop (@FINITE a0 (@UNIONS a0 x0)).
Definition term49 (a0 : Type') (x0 : type686 a0) := (@FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 (@UNIONS a0 x0)) y1))) -> @FINITE (a0 -> Prop) x0.
Definition term87 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := exists y0 : a0 -> Prop, @SETSPEC (a0 -> Prop) x0 ((fun y1 : a0 -> Prop => forall y2 : a0, (@IN a0 y2 y1) -> @IN a0 y2 (@UNIONS a0 x1)) y0) y0.
Definition term4 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> @FINITE a0 x0.
Definition term24 (x0 : Prop) (x1 : Prop) := (~ x0) -> ~ x1.
Definition term119 (a0 : Type') := fun y0 : type686 a0 => (~ (forall y1 : a0 -> Prop, (y0 y1) -> forall y2 : a0, (y1 y2) -> exists y3 : a0 -> Prop, (y0 y3) /\ (y3 y2))) -> False.
Definition term29 (a0 : Type') (x0 : type686 a0) := ~ (@FINITE (a0 -> Prop) x0).
Definition term50 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := (@SUBSET (a0 -> Prop) x1 x0) -> (@FINITE (a0 -> Prop) x0) -> @FINITE (a0 -> Prop) x1.
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@SUBSET a0 x1 x0) -> (@FINITE a0 x0) -> @FINITE a0 x1.
Definition term79 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x1 y1) y1)).
Definition term86 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := fun y0 : a0 -> Prop => @SETSPEC (a0 -> Prop) x0 ((fun y1 : a0 -> Prop => forall y2 : a0, (@IN a0 y2 y1) -> @IN a0 y2 (@UNIONS a0 x1)) y0) y0.
Definition term42 (a0 : Type') (x0 : type686 a0) := (@FINITE a0 (@UNIONS a0 x0)) -> @FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 (@UNIONS a0 x0)) y1)).
Definition term151 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := ((@I ((a0 -> Prop) -> Prop) x0 x1) /\ (@I (a0 -> Prop) x1 x2)) -> False.
Definition term145 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (~ (@I ((a0 -> Prop) -> Prop) x0 x1)) -> @I ((a0 -> Prop) -> Prop) x0 x1.
Definition term6 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> @FINITE a0 x0.
Definition term97 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := and (x0 x1).
Definition term85 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 ((fun y0 : a0 -> Prop => forall y1 : a0, (@IN a0 y1 y0) -> @IN a0 y1 (@UNIONS a0 x1)) x2) x2.
Definition term114 (a0 : Type') (x0 : type686 a0) := ((~ (forall y0 : a0 -> Prop, (x0 y0) -> forall y1 : a0, (y0 y1) -> exists y2 : a0 -> Prop, (x0 y2) /\ (y2 y1))) -> False) -> (~ (forall y0 : a0 -> Prop, (x0 y0) -> forall y1 : a0, (y0 y1) -> exists y2 : a0 -> Prop, (x0 y2) /\ (y2 y1))) -> False.
Definition term139 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := or (~ (x0 x1)).
Definition term83 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => forall y1 : a0, (@IN a0 y1 y0) -> @IN a0 y1 (@UNIONS a0 x0).
Definition term105 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := fun y0 : a0 => (@IN a0 y0 x0) -> @IN a0 y0 (@UNIONS a0 x1).
Definition term129 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, ~ ((fun y1 : a0 -> Prop => (x0 y1) /\ (y1 x1)) y0).
Definition term57 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := @SUBSET a0 x0 (@UNIONS a0 x1).
Definition term132 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => ~ ((fun y1 : a0 -> Prop => (x0 y1) /\ (y1 x1)) y0).
Definition term127 (a0 : Type') (x0 : type686 a0) := ~ (ex x0).
Definition term47 (a0 : Type') (x0 : type686 a0) := (~ (@FINITE (a0 -> Prop) x0)) -> (@FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 (@UNIONS a0 x0)) y1))) -> False.
Definition term96 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := and (@IN (a0 -> Prop) x0 x1).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) -> @FINITE a0 x1.
Definition term121 (a0 : Type') := forall y0 : type686 a0, (~ (forall y1 : a0 -> Prop, (y0 y1) -> forall y2 : a0, (y1 y2) -> exists y3 : a0 -> Prop, (y0 y3) /\ (y3 y2))) -> False.
Definition term72 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := imp (@IN (a0 -> Prop) x0 x1).
Definition term99 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (x0 x1) /\ (x1 x2).
Definition term30 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => (@FINITE (a0 -> Prop) y0) -> (@FINITE a0 (@UNIONS a0 y0)) = (forall y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 y0) -> @FINITE a0 y1)) x0.
Definition term19 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@SUBSET a0 y1 y0) -> (@FINITE a0 y0) -> @FINITE a0 y1) x0.
Definition term12 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@SUBSET a0 y0 y1) -> (@FINITE a0 y1) -> @FINITE a0 y0) x0.
Definition term84 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 ((fun y0 : a0 -> Prop => forall y1 : a0, (@IN a0 y1 y0) -> @IN a0 y1 (@UNIONS a0 x1)) x2).
Definition term117 (a0 : Type') (x0 : type686 a0) := ~ (~ (forall y0 : a0 -> Prop, (x0 y0) -> forall y1 : a0, (y0 y1) -> exists y2 : a0 -> Prop, (x0 y2) /\ (y2 y1))).
Definition term112 (a0 : Type') (x0 : type686 a0) := (~ (forall y0 : a0 -> Prop, (x0 y0) -> forall y1 : a0, (y0 y1) -> exists y2 : a0 -> Prop, (x0 y2) /\ (y2 y1))) -> False.
Definition term55 (a0 : Type') (x0 : type686 a0) := @SUBSET (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 (@UNIONS a0 x0)) y1)).
Definition term156 (a0 : Type') := forall y0 : type686 a0, (@FINITE a0 (@UNIONS a0 y0)) = ((@FINITE (a0 -> Prop) y0) /\ (forall y1 : a0 -> Prop, (@IN (a0 -> Prop) y1 y0) -> @FINITE a0 y1)).
Definition term35 (a0 : Type') (x0 : type686 a0) := @eq Prop (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> @FINITE a0 y0).
Definition term51 (a0 : Type') (x0 : type686 a0) := (@SUBSET (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 (@UNIONS a0 x0)) y1))) -> (@FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 (@UNIONS a0 x0)) y1))) -> @FINITE (a0 -> Prop) x0.
Definition term107 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := forall y0 : a0, (x0 y0) -> exists y1 : a0 -> Prop, (x1 y1) /\ (y1 y0).
Definition term91 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := @eq Prop (@IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (forall y2 : a0, (@IN a0 y2 y1) -> @IN a0 y2 (@UNIONS a0 x1)) y1))).
Definition term90 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := @eq Prop (@IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => forall y3 : a0, (@IN a0 y3 y2) -> @IN a0 y3 (@UNIONS a0 x1)) y1) y1))).
Definition term115 (a0 : Type') (x0 : type686 a0) := (((~ (forall y0 : a0 -> Prop, (x0 y0) -> forall y1 : a0, (y0 y1) -> exists y2 : a0 -> Prop, (x0 y2) /\ (y2 y1))) -> False) -> (~ (forall y0 : a0 -> Prop, (x0 y0) -> forall y1 : a0, (y0 y1) -> exists y2 : a0 -> Prop, (x0 y2) /\ (y2 y1))) -> False) -> (~ (forall y0 : a0 -> Prop, (x0 y0) -> forall y1 : a0, (y0 y1) -> exists y2 : a0 -> Prop, (x0 y2) /\ (y2 y1))) -> False.
Definition term60 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : type686 a0) := @SETSPEC (a0 -> Prop) x0 (forall y0 : a0, (@IN a0 y0 x1) -> @IN a0 y0 (@UNIONS a0 x2)).
Definition term33 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> @FINITE a0 y0.
Definition term0 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) -> x2.
Definition term92 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@SUBSET a0 y0 x0) -> (@FINITE a0 x0) -> @FINITE a0 y0) x1.
Definition term13 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@SUBSET a0 x0 y0) -> (@FINITE a0 y0) -> @FINITE a0 x0) x1.
Definition term89 (a0 : Type') (x0 : type686 a0) := @GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => forall y3 : a0, (@IN a0 y3 y2) -> @IN a0 y3 (@UNIONS a0 x0)) y1) y1).
Definition term69 (a0 : Type') (x0 : type686 a0) := @GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (forall y2 : a0, (@IN a0 y2 y1) -> @IN a0 y2 (@UNIONS a0 x0)) y1).
Definition term52 (a0 : Type') (x0 : type686 a0) := @GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 (@UNIONS a0 x0)) y1).
Definition term136 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (@I (a0 -> Prop) x0 x1).
Definition term17 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (@SUBSET a0 y1 y0) -> (@FINITE a0 y0) -> @FINITE a0 y1.
Definition term11 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (@SUBSET a0 y0 y1) -> (@FINITE a0 y1) -> @FINITE a0 y0.
Definition term10 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0.
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 (@SUBSET a0 x2 (@UNIONS a0 x1)) x2.
Definition term58 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 (@UNIONS a0 x1).
Definition term142 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => (~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (~ (@I (a0 -> Prop) y0 x1)).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (@SUBSET a0 x0 y0) -> (@FINITE a0 y0) -> @FINITE a0 x0.
Definition term108 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := (x1 x0) -> forall y0 : a0, (x0 y0) -> exists y1 : a0 -> Prop, (x1 y1) /\ (y1 y0).
Definition term122 (a0 : Type') := forall y0 : type686 a0, forall y1 : a0 -> Prop, (y0 y1) -> forall y2 : a0, (y1 y2) -> exists y3 : a0 -> Prop, (y0 y3) /\ (y3 y2).
Definition term64 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := fun y0 : a0 -> Prop => @SETSPEC (a0 -> Prop) x0 (forall y1 : a0, (@IN a0 y1 y0) -> @IN a0 y1 (@UNIONS a0 x1)) y0.
Definition term93 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := imp (x0 x1).
Definition term141 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := (~ (@I ((a0 -> Prop) -> Prop) x0 x1)) \/ (~ (@I (a0 -> Prop) x1 x2)).
Definition term130 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (x0 y0) /\ (y0 x1)) x2.
Definition term144 (a0 : Type') (x0 : type686 a0) (x1 : a0) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (~ (@I (a0 -> Prop) y0 x1))) x2.
Definition term110 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, (x0 y0) -> forall y1 : a0, (y0 y1) -> exists y2 : a0 -> Prop, (x0 y2) /\ (y2 y1).
Definition term109 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => (x0 y0) -> forall y1 : a0, (y0 y1) -> exists y2 : a0 -> Prop, (x0 y2) /\ (y2 y1).
Definition term106 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := fun y0 : a0 => (x0 y0) -> exists y1 : a0 -> Prop, (x1 y1) /\ (y1 y0).
Definition term76 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) -> @IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (forall y3 : a0, (@IN a0 y3 y2) -> @IN a0 y3 (@UNIONS a0 x0)) y2)).
Definition term75 (a0 : Type') (x0 : type686 a0) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 x0) -> @IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 (@UNIONS a0 x0)) y2)).
Definition term81 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := @IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => forall y3 : a0, (@IN a0 y3 y2) -> @IN a0 y3 (@UNIONS a0 x1)) y1) y1)).
Definition term80 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := @IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (x1 y1) y1)).
Definition term71 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := @IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (forall y2 : a0, (@IN a0 y2 y1) -> @IN a0 y2 (@UNIONS a0 x1)) y1)).
Definition term70 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := @IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 (@UNIONS a0 x1)) y1)).
Definition term41 (a0 : Type') (x0 : type686 a0) := ~ (@FINITE a0 (@UNIONS a0 x0)).
Definition term23 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => ((~ x0) -> ~ y0) = (y0 -> x0)) x1.
Definition term40 (a0 : Type') (x0 : type686 a0) := False /\ (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> @FINITE a0 y0).
Definition term53 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 x1.
Definition term143 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, (~ (@I ((a0 -> Prop) -> Prop) x0 y0)) \/ (~ (@I (a0 -> Prop) y0 x1)).
Definition term36 (a0 : Type') (x0 : type686 a0) := and (@FINITE (a0 -> Prop) x0).
Definition term116 (a0 : Type') (x0 : type686 a0) := (((~ (forall y0 : a0 -> Prop, (x0 y0) -> forall y1 : a0, (y0 y1) -> exists y2 : a0 -> Prop, (x0 y2) /\ (y2 y1))) -> False) -> (~ (forall y0 : a0 -> Prop, (x0 y0) -> forall y1 : a0, (y0 y1) -> exists y2 : a0 -> Prop, (x0 y2) /\ (y2 y1))) -> False) -> ((~ (forall y0 : a0 -> Prop, (x0 y0) -> forall y1 : a0, (y0 y1) -> exists y2 : a0 -> Prop, (x0 y2) /\ (y2 y1))) -> False) -> (~ (forall y0 : a0 -> Prop, (x0 y0) -> forall y1 : a0, (y0 y1) -> exists y2 : a0 -> Prop, (x0 y2) /\ (y2 y1))) -> False.
Definition term137 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ~ (x0 x1).
Definition term46 (a0 : Type') (x0 : type686 a0) := imp (~ (@FINITE (a0 -> Prop) x0)).
Definition term32 (a0 : Type') (x0 : type686 a0) := @FINITE a0 (@UNIONS a0 x0).
Definition term45 (a0 : Type') (x0 : type686 a0) := ~ (@FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 (@UNIONS a0 x0)) y1))).
Definition term124 (a0 : Type') (x0 : type686 a0) (x1 : a0) := ~ (exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x1)).
Definition term101 (a0 : Type') (x0 : type686 a0) (x1 : a0) := fun y0 : a0 -> Prop => (x0 y0) /\ (y0 x1).
Definition term104 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : a0) := (x0 x2) -> exists y0 : a0 -> Prop, (x1 y0) /\ (y0 x2).
Definition term65 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := exists y0 : a0 -> Prop, @SETSPEC (a0 -> Prop) x0 (@SUBSET a0 y0 (@UNIONS a0 x1)) y0.
Definition term125 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x0 x1) /\ (x1 x2)).
Definition term102 (a0 : Type') (x0 : type686 a0) (x1 : a0) := exists y0 : a0 -> Prop, (x0 y0) /\ (y0 x1).
Definition term38 (a0 : Type') (x0 : type686 a0) := True /\ (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> @FINITE a0 y0).
Definition term138 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := ~ (@I ((a0 -> Prop) -> Prop) x0 x1).
Definition term15 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (@SUBSET a0 y0 y1) -> (@FINITE a0 y1) -> @FINITE a0 y0) -> (@FINITE a0 x0) -> @FINITE a0 x1.
Definition term150 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) (x2 : a0) := ~ ((@I ((a0 -> Prop) -> Prop) x0 x1) /\ (@I (a0 -> Prop) x1 x2)).
Definition term39 (a0 : Type') (x0 : type686 a0) := (~ (@FINITE (a0 -> Prop) x0)) -> (@FINITE (a0 -> Prop) x0) = False.
