Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term201 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0, forall y2 : a0, ((y0 y1) /\ ((y0 y2) /\ (forall y3 : a0, (y3 = y1) = (y3 = y2)))) -> y1 = y2.
Definition term150 (a0 : Type') (x0 : a0 -> Prop) := (forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x0) /\ ((@IN a0 y1 x0) /\ (((fun y2 : a0 => @INSERT a0 y2 (@EMPTY a0)) y0) = ((fun y2 : a0 => @INSERT a0 y2 (@EMPTY a0)) y1)))) -> y0 = y1) -> (@FINITE (a0 -> Prop) (@IMAGE a0 (a0 -> Prop) (fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0)) = (@FINITE a0 x0).
Definition term162 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (@IN a0 x1 x0) /\ ((@IN a0 x2 x0) /\ (forall y0 : a0, (@IN a0 y0 (@INSERT a0 x1 (@EMPTY a0))) = (@IN a0 y0 (@INSERT a0 x2 (@EMPTY a0))))).
Definition term146 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ((@IN a0 x0 x1) -> (@IN (a0 -> Prop) ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x1) y1))) = True) -> ((@IN a0 x0 x1) -> @IN (a0 -> Prop) ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x1) y1))) = ((@IN a0 x0 x1) -> True).
Definition term38 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0.
Definition term18 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x0 y2) y2))) = (x0 y0).
Definition term252 := (~ False) -> False.
Definition term31 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> x1 -> x2.
Definition term190 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => forall y1 : a0, ((x0 y0) /\ ((x0 y1) /\ (forall y2 : a0, (y2 = y0) = (y2 = y1)))) -> y0 = y1.
Definition term172 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => forall y1 : a0, ((@IN a0 y0 x0) /\ ((@IN a0 y1 x0) /\ (forall y2 : a0, (@IN a0 y2 (@INSERT a0 y0 (@EMPTY a0))) = (@IN a0 y2 (@INSERT a0 y1 (@EMPTY a0)))))) -> y0 = y1.
Definition term171 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => forall y1 : a0, ((@IN a0 y0 x0) /\ ((@IN a0 y1 x0) /\ (((fun y2 : a0 => @INSERT a0 y2 (@EMPTY a0)) y0) = ((fun y2 : a0 => @INSERT a0 y2 (@EMPTY a0)) y1)))) -> y0 = y1.
Definition term79 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 (@IMAGE a0 (a0 -> Prop) (fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) x0)) -> (fun y1 : a0 -> Prop => @IN (a0 -> Prop) y1 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 (@SUBSET a0 y3 x0) y3))) y0.
Definition term17 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y0 y3) y3))) = (y0 y1)) x0.
Definition term132 (a0 : Type') := fun y0 : a0 => (fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) y0.
Definition term52 (a0 : Type') (x0 : a0 -> Prop) := @FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x0) y1)).
Definition term199 (x0 : Prop) := ~ (~ x0).
Definition term69 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) (x2 : type1402 a0) := forall y0 : a0, (@IN a0 y0 x0) -> x1 (x2 y0).
Definition term106 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => @SUBSET a0 y0 x0) x1.
Definition term250 (a0 : Type') (x0 : a0) (x1 : a0) := (~ (x0 = x1)) -> x0 = x1.
Definition term217 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := (fun y0 : a0 => (y0 = x0) \/ (~ (y0 = x1))) x2.
Definition term107 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 ((fun y0 : a0 -> Prop => @SUBSET a0 y0 x1) x2).
Definition term118 (a0 : Type') (x0 : a0) := @IN (a0 -> Prop) ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0).
Definition term177 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (x1 = x0) \/ (@IN a0 x1 x2).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> @FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 y0) y2))) x0.
Definition term144 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term248 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := (x1 = x0) -> x1 = x2.
Definition term33 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) -> (@SUBSET a0 x1 x0) -> @FINITE a0 x1.
Definition term226 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop (forall y0 : a0, ((y0 = x0) \/ (~ (y0 = x1))) /\ ((~ (y0 = x0)) \/ (y0 = x1))).
Definition term230 (a0 : Type') (x0 : a0) (x1 : a0) := and (forall y0 : a0, (fun y1 : a0 => (y1 = x0) \/ (~ (y1 = x1))) y0).
Definition term176 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := @IN a0 x0 (@INSERT a0 x1 x2).
Definition term224 (a0 : Type') (x0 : a0) (x1 : a0) := fun y0 : a0 => ((fun y1 : a0 => (y1 = x0) \/ (~ (y1 = x1))) y0) /\ ((fun y1 : a0 => (~ (y1 = x0)) \/ (y1 = x1)) y0).
Definition term14 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => (@IN a0 x0 (@INSERT a0 y0 (@EMPTY a0))) = (x0 = y0)) x1.
Definition term192 (x0 : Prop) := (~ x0) -> False.
Definition term136 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) (x3 : Prop) := ((x1 = x2) -> (@IN a0 x1 x0) = x3) -> ((@IN a0 x1 ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x2)) -> @IN a0 x1 x0) = ((x1 = x2) -> x3).
Definition term251 (a0 : Type') (x0 : a0) (x1 : a0) := (x0 = x1) -> False.
Definition term116 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x0) y1.
Definition term115 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => @SUBSET a0 y2 x0) y1) y1.
Definition term63 (a0 : Type') (x0 : a0 -> Prop) := (@SUBSET (a0 -> Prop) (@IMAGE a0 (a0 -> Prop) (fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x0) y1))) -> @FINITE (a0 -> Prop) (@IMAGE a0 (a0 -> Prop) (fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0).
Definition term138 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ((x1 = x2) -> (@IN a0 x1 x0) = True) -> ((@IN a0 x1 ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x2)) -> @IN a0 x1 x0) = ((x1 = x2) -> True).
Definition term242 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := @eq Prop ((x1 = x0) \/ (~ (x1 = x2))).
Definition term180 (a0 : Type') (x0 : a0) (x1 : a0) := (x0 = x1) \/ False.
Definition term139 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0)) -> @IN a0 x1 x2.
Definition term143 (a0 : Type') := forall y0 : a0, True.
Definition term65 (a0 : Type') (x0 : type686 a0) (x1 : type686 a0) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> @IN (a0 -> Prop) y0 x1.
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> Prop, (forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ ((@IN a0 y2 y0) /\ ((x0 y1) = (x0 y2)))) -> y1 = y2) -> (@FINITE a1 (@IMAGE a0 a1 x0 y0)) = (@FINITE a0 y0).
Definition term219 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := and ((fun y0 : a0 => (y0 = x0) \/ (~ (y0 = x1))) x2).
Definition term133 (a0 : Type') (x0 : a0) := @eq (a0 -> Prop) ((fun y0 : a0 => (fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) y0) x0).
Definition term164 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := imp ((@IN a0 x1 x0) /\ ((@IN a0 x2 x0) /\ (forall y0 : a0, (@IN a0 y0 (@INSERT a0 x1 (@EMPTY a0))) = (@IN a0 y0 (@INSERT a0 x2 (@EMPTY a0)))))).
Definition term32 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := ((@FINITE a0 x0) /\ (@SUBSET a0 x1 x0)) -> @FINITE a0 x1.
Definition term47 (a0 : Type') := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> forall y1 : a0 -> Prop, (@SUBSET a0 y1 y0) -> @FINITE a0 y1.
Definition term209 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (x0 x2) /\ (forall y0 : a0, ((y0 = x1) \/ (~ (y0 = x2))) /\ ((~ (y0 = x1)) \/ (y0 = x2))).
Definition term184 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (x0 x2) /\ (forall y0 : a0, (y0 = x1) = (y0 = x2)).
Definition term147 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 x1) -> True.
Definition term233 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : a0, (fun y1 : a0 => (~ (y1 = x0)) \/ (y1 = x1)) y0.
Definition term228 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : a0, (fun y1 : a0 => (y1 = x0) \/ (~ (y1 = x1))) y0.
Definition term243 (x0 : Prop) (x1 : Prop) := (~ x0) -> x1.
Definition term62 (a0 : Type') (x0 : a0 -> Prop) := (forall y0 : type686 a0, (@SUBSET (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 x0) y2))) -> @FINITE (a0 -> Prop) y0) -> forall y0 : type686 a0, (@SUBSET (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 x0) y2))) -> @FINITE (a0 -> Prop) y0.
Definition term189 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, ((x0 x1) /\ ((x0 y0) /\ (forall y1 : a0, (y1 = x1) = (y1 = y0)))) -> x1 = y0.
Definition term170 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, ((@IN a0 x1 x0) /\ ((@IN a0 y0 x0) /\ (forall y1 : a0, (@IN a0 y1 (@INSERT a0 x1 (@EMPTY a0))) = (@IN a0 y1 (@INSERT a0 y0 (@EMPTY a0)))))) -> x1 = y0.
Definition term169 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := forall y0 : a0, ((@IN a0 x1 x0) /\ ((@IN a0 y0 x0) /\ (((fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) x1) = ((fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) y0)))) -> x1 = y0.
Definition term153 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop (@IN a0 x0 ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x1)).
Definition term37 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@SUBSET a0 x0 y0) -> @FINITE a0 x0.
Definition term82 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 (@IMAGE a0 (a0 -> Prop) (fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) x0)) -> @IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 x0) y2))).
Definition term64 (a0 : Type') (x0 : a0 -> Prop) := @IMAGE a0 (a0 -> Prop) (fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0.
Definition term51 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> @FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x0) y1)).
Definition term8 (a0 : Type') (a1 : Type') := (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ ((y0 y2) = (y0 y3)))) -> y2 = y3) -> (@FINITE a1 (@IMAGE a0 a1 y0 y1)) = (@FINITE a0 y1)) -> forall y0 : a0 -> a1, forall y1 : a0 -> Prop, (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ ((y0 y2) = (y0 y3)))) -> y2 = y3) -> (@FINITE a1 (@IMAGE a0 a1 y0 y1)) = (@FINITE a0 y1).
Definition term256 (a0 : Type') (x0 : a0 -> Prop) := ((@FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x0) y1))) -> @FINITE a0 x0) /\ ((@FINITE a0 x0) -> @FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x0) y1))).
Definition term151 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term114 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0 -> Prop, @SETSPEC (a0 -> Prop) x0 (@SUBSET a0 y0 x1) y0.
Definition term240 (x0 : Prop) := (~ x0) -> x0.
Definition term235 (a0 : Type') (x0 : a0) (x1 : a0) := (forall y0 : a0, (y0 = x0) \/ (~ (y0 = x1))) /\ (forall y0 : a0, (~ (y0 = x0)) \/ (y0 = x1)).
Definition term206 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := ((x1 = x0) \/ (~ (x1 = x2))) /\ ((~ (x1 = x0)) \/ (x1 = x2)).
Definition term161 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (@IN a0 x1 x0) /\ ((@IN a0 x2 x0) /\ (((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x1) = ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x2))).
Definition term163 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := imp ((@IN a0 x1 x0) /\ ((@IN a0 x2 x0) /\ (((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x1) = ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x2)))).
Definition term137 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := (x1 = x0) -> (@IN a0 x1 x2) = True.
Definition term215 (a0 : Type') (x0 : a0) (x1 : a0) := fun y0 : a0 => (y0 = x0) \/ (~ (y0 = x1)).
Definition term103 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 -> Prop => @SUBSET a0 y0 x0) ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x1).
Definition term74 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => @IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 x0) y2))) x1.
Definition term90 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) -> @IN (a0 -> Prop) ((fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) y0) (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 x0) y2)).
Definition term168 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => ((@IN a0 x1 x0) /\ ((@IN a0 y0 x0) /\ (forall y1 : a0, (@IN a0 y1 (@INSERT a0 x1 (@EMPTY a0))) = (@IN a0 y1 (@INSERT a0 y0 (@EMPTY a0)))))) -> x1 = y0.
Definition term12 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, (@IN a0 y0 (@INSERT a0 y1 (@EMPTY a0))) = (y0 = y1)) x0.
Definition term39 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@SUBSET a0 y0 y1) -> @FINITE a0 y0.
Definition term216 (a0 : Type') (x0 : a0) (x1 : a0) := fun y0 : a0 => (~ (y0 = x0)) \/ (y0 = x1).
Definition term125 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@IN a0 x1 ((fun y2 : a0 => @INSERT a0 y2 (@EMPTY a0)) x0)) = y0) -> (y0 -> (@IN a0 x1 x2) = y1) -> ((@IN a0 x1 ((fun y2 : a0 => @INSERT a0 y2 (@EMPTY a0)) x0)) -> @IN a0 x1 x2) = (y0 -> y1)) x3.
Definition term212 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (forall y0 : a0, x0 y0) /\ (forall y0 : a0, x1 y0).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (forall y1 : a0, forall y2 : a0, ((@IN a0 y1 y0) /\ ((@IN a0 y2 y0) /\ ((x0 y1) = (x0 y2)))) -> y1 = y2) -> (@FINITE a1 (@IMAGE a0 a1 x0 y0)) = (@FINITE a0 y0)) x1.
Definition term222 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := (~ (x1 = x0)) \/ (x1 = x2).
Definition term57 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : type686 a0, (@SUBSET (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 x0) y2))) -> @FINITE (a0 -> Prop) y0.
Definition term78 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@IN (a0 -> Prop) x0 (@IMAGE a0 (a0 -> Prop) (fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x1)) -> @IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x1) y1)).
Definition term21 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> a0) := (fun y0 : a1 -> a0 => forall y1 : a1 -> Prop, (forall y2 : a0, (@IN a0 y2 (@IMAGE a1 a0 y0 y1)) -> x0 y2) = (forall y2 : a1, (@IN a1 y2 y1) -> x0 (y0 y2))) x1.
Definition term237 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (x0 x1) /\ ((x0 x2) /\ ((forall y0 : a0, (y0 = x1) \/ (~ (y0 = x2))) /\ (forall y0 : a0, (~ (y0 = x1)) \/ (y0 = x2)))).
Definition term244 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := (~ (~ (x1 = x0))) -> x1 = x2.
Definition term229 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : a0, (y0 = x0) \/ (~ (y0 = x1)).
Definition term113 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0 -> Prop, @SETSPEC (a0 -> Prop) x0 ((fun y1 : a0 -> Prop => @SUBSET a0 y1 x1) y0) y0.
Definition term58 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := (fun y0 : type686 a0 => (@SUBSET (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 x0) y2))) -> @FINITE (a0 -> Prop) y0) x1.
Definition term213 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : a0, ((fun y1 : a0 => (y1 = x0) \/ (~ (y1 = x1))) y0) /\ ((fun y1 : a0 => (~ (y1 = x0)) \/ (y1 = x1)) y0).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> @FINITE a0 x0.
Definition term182 (a0 : Type') (x0 : a0) (x1 : a0) := fun y0 : a0 => (y0 = x0) = (y0 = x1).
Definition term236 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (x0 x2) /\ ((forall y0 : a0, (y0 = x1) \/ (~ (y0 = x2))) /\ (forall y0 : a0, (~ (y0 = x1)) \/ (y0 = x2))).
Definition term187 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ((x0 x1) /\ ((x0 x2) /\ (forall y0 : a0, (y0 = x1) = (y0 = x2)))) -> x1 = x2.
Definition term22 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> a0) := forall y0 : a1 -> Prop, (forall y1 : a0, (@IN a0 y1 (@IMAGE a1 a0 x1 y0)) -> x0 y1) = (forall y1 : a1, (@IN a1 y1 y0) -> x0 (x1 y1)).
Definition term157 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : a0, (@IN a0 y0 (@INSERT a0 x0 (@EMPTY a0))) = (@IN a0 y0 (@INSERT a0 x1 (@EMPTY a0))).
Definition term91 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term124 (a0 : Type') (x0 : a0) (x1 : a0) := @IN a0 x0 ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x1).
Definition term20 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x1 y1) y1)).
Definition term111 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => @SETSPEC (a0 -> Prop) x0 ((fun y1 : a0 -> Prop => @SUBSET a0 y1 x1) y0) y0.
Definition term156 (a0 : Type') (x0 : a0) (x1 : a0) := fun y0 : a0 => (@IN a0 y0 (@INSERT a0 x0 (@EMPTY a0))) = (@IN a0 y0 (@INSERT a0 x1 (@EMPTY a0))).
Definition term155 (a0 : Type') (x0 : a0) (x1 : a0) := fun y0 : a0 => (@IN a0 y0 ((fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) x0)) = (@IN a0 y0 ((fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) x1)).
Definition term11 (x0 : Prop) (x1 : Prop) := ((x0 = x1) -> x0 -> x1) -> (x0 = x1) -> x0 -> x1.
Definition term77 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@IN (a0 -> Prop) x1 (@IMAGE a0 (a0 -> Prop) (fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0)) -> (fun y0 : a0 -> Prop => @IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 x0) y2))) x1.
Definition term55 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x0) y1))) -> forall y0 : type686 a0, (@SUBSET (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 x0) y2))) -> @FINITE (a0 -> Prop) y0.
Definition term53 (a0 : Type') (x0 : a0 -> Prop) := @FINITE (a0 -> Prop) (@IMAGE a0 (a0 -> Prop) (fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0).
Definition term239 (a0 : Type') (x0 : a0) := ~ (x0 = x0).
Definition term158 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@IN a0 x0 x1).
Definition term218 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := (x1 = x0) \/ (~ (x1 = x2)).
Definition term208 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : a0, ((y0 = x0) \/ (~ (y0 = x1))) /\ ((~ (y0 = x0)) \/ (y0 = x1)).
Definition term36 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((@FINITE a0 y0) /\ (@SUBSET a0 x0 y0)) -> @FINITE a0 x0.
Definition term195 (a0 : Type') (x0 : a0 -> Prop) := ((~ (forall y0 : a0, forall y1 : a0, ((x0 y0) /\ ((x0 y1) /\ (forall y2 : a0, (y2 = y0) = (y2 = y1)))) -> y0 = y1)) -> False) -> (~ (forall y0 : a0, forall y1 : a0, ((x0 y0) /\ ((x0 y1) /\ (forall y2 : a0, (y2 = y0) = (y2 = y1)))) -> y0 = y1)) -> False.
Definition term183 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : a0, (y0 = x0) = (y0 = x1).
Definition term141 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 ((fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) x0)) -> @IN a0 y0 x1.
Definition term70 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 (@IMAGE a0 (a0 -> Prop) (fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) x0)) -> (fun y1 : a0 -> Prop => @IN (a0 -> Prop) y1 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 (@SUBSET a0 y3 x0) y3))) y0.
Definition term129 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term128 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) (x4 : Prop) := ((@IN a0 x1 ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0)) = x3) -> (x3 -> (@IN a0 x1 x2) = x4) -> ((@IN a0 x1 ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0)) -> @IN a0 x1 x2) = (x3 -> x4).
Definition term159 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (@IN a0 x2 x0) /\ (((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x1) = ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x2)).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> forall y1 : a0 -> Prop, (@SUBSET a0 y1 y0) -> @FINITE a0 y1) x0.
Definition term227 (a0 : Type') (x0 : a0) (x1 : a0) := fun y0 : a0 => (fun y1 : a0 => (y1 = x0) \/ (~ (y1 = x1))) y0.
Definition term9 (x0 : Prop) (x1 : Prop) := (x0 = x1) -> x0 -> x1.
Definition term142 (a0 : Type') := fun y0 : a0 => True.
Definition term130 (a0 : Type') (x0 : type1402 a0) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term109 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 ((fun y0 : a0 -> Prop => @SUBSET a0 y0 x1) x2) x2.
Definition term54 (a0 : Type') (x0 : type686 a0) := (@FINITE (a0 -> Prop) x0) -> forall y0 : type686 a0, (@SUBSET (a0 -> Prop) y0 x0) -> @FINITE (a0 -> Prop) y0.
Definition term46 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE a0 x0) -> forall y0 : a0 -> Prop, (@SUBSET a0 y0 x0) -> @FINITE a0 y0.
Definition term175 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (x0 x1).
Definition term97 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((@IN a0 x0 x1) = x2) -> (x2 -> (@IN (a0 -> Prop) ((fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) x0) (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 x1) y2))) = y0) -> ((@IN a0 x0 x1) -> @IN (a0 -> Prop) ((fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) x0) (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 x1) y2))) = (x2 -> y0)) x3.
Definition term188 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => ((x0 x1) /\ ((x0 y0) /\ (forall y1 : a0, (y1 = x1) = (y1 = y0)))) -> x1 = y0.
Definition term98 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : Prop) (x3 : Prop) := ((@IN a0 x0 x1) = x2) -> (x2 -> (@IN (a0 -> Prop) ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x1) y1))) = x3) -> ((@IN a0 x0 x1) -> @IN (a0 -> Prop) ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x1) y1))) = (x2 -> x3).
Definition term149 (a0 : Type') (x0 : type1402 a0) (x1 : a0 -> Prop) := (forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x1) /\ ((@IN a0 y1 x1) /\ ((x0 y0) = (x0 y1)))) -> y0 = y1) -> (@FINITE (a0 -> Prop) (@IMAGE a0 (a0 -> Prop) x0 x1)) = (@FINITE a0 x1).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x1) /\ ((@IN a0 y1 x1) /\ ((x0 y0) = (x0 y1)))) -> y0 = y1) -> (@FINITE a1 (@IMAGE a0 a1 x0 x1)) = (@FINITE a0 x1).
Definition term148 (a0 : Type') (x0 : a0 -> Prop) := ((@FINITE (a0 -> Prop) (@IMAGE a0 (a0 -> Prop) (fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0)) = (@FINITE a0 x0)) -> (@FINITE (a0 -> Prop) (@IMAGE a0 (a0 -> Prop) (fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0)) -> @FINITE a0 x0.
Definition term88 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 x0) -> (fun y1 : a0 -> Prop => @IN (a0 -> Prop) y1 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 (@SUBSET a0 y3 x0) y3))) ((fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) y0).
Definition term42 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@SUBSET a0 y0 y1) -> @FINITE a0 y0) x0.
Definition term26 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@SUBSET a0 y0 y1) = (forall y2 : a0, (@IN a0 y2 y0) -> @IN a0 y2 y1)) x0.
Definition term131 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) y0) x0.
Definition term145 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 x1) -> (@IN (a0 -> Prop) ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x1) y1))) = True.
Definition term198 (a0 : Type') (x0 : a0 -> Prop) := ~ (~ (forall y0 : a0, forall y1 : a0, ((x0 y0) /\ ((x0 y1) /\ (forall y2 : a0, (y2 = y0) = (y2 = y1)))) -> y0 = y1)).
Definition term59 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := (@SUBSET (a0 -> Prop) x1 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x0) y1))) -> @FINITE (a0 -> Prop) x1.
Definition term193 (a0 : Type') (x0 : a0 -> Prop) := (~ (forall y0 : a0, forall y1 : a0, ((x0 y0) /\ ((x0 y1) /\ (forall y2 : a0, (y2 = y0) = (y2 = y1)))) -> y0 = y1)) -> False.
Definition term160 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (@IN a0 x2 x0) /\ (forall y0 : a0, (@IN a0 y0 (@INSERT a0 x1 (@EMPTY a0))) = (@IN a0 y0 (@INSERT a0 x2 (@EMPTY a0)))).
Definition term60 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := @SUBSET (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x1) y1)).
Definition term81 (a0 : Type') (x0 : a0 -> Prop) := @eq Prop (forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 (@IMAGE a0 (a0 -> Prop) (fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) x0)) -> (fun y1 : a0 -> Prop => @IN (a0 -> Prop) y1 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 (@SUBSET a0 y3 x0) y3))) y0).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := @FINITE a1 (@IMAGE a0 a1 x0 x1).
Definition term154 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop (@IN a0 x0 (@INSERT a0 x1 (@EMPTY a0))).
Definition term126 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := forall y0 : Prop, ((@IN a0 x1 ((fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) x0)) = x3) -> (x3 -> (@IN a0 x1 x2) = y0) -> ((@IN a0 x1 ((fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) x0)) -> @IN a0 x1 x2) = (x3 -> y0).
Definition term96 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : Prop) := forall y0 : Prop, ((@IN a0 x0 x1) = x2) -> (x2 -> (@IN (a0 -> Prop) ((fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) x0) (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 x1) y2))) = y0) -> ((@IN a0 x0 x1) -> @IN (a0 -> Prop) ((fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) x0) (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 x1) y2))) = (x2 -> y0).
Definition term92 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term66 (a0 : Type') (x0 : a0 -> Prop) := @SUBSET (a0 -> Prop) (@IMAGE a0 (a0 -> Prop) (fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x0) y1)).
Definition term83 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 -> Prop => @IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 x0) y2))) ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x1).
Definition term254 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE (a0 -> Prop) (@IMAGE a0 (a0 -> Prop) (fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0)) -> @FINITE a0 x0.
Definition term234 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : a0, (~ (y0 = x0)) \/ (y0 = x1).
Definition term87 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@IN a0 x0 x1) -> @IN (a0 -> Prop) ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x1) y1)).
Definition term204 (a0 : Type') (x0 : a0) (x1 : a0) := (~ (x0 = x1)) -> False.
Definition term35 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@SUBSET a0 x0 y0) -> @FINITE a0 x0.
Definition term68 (a0 : Type') (x0 : type1402 a0) (x1 : a0 -> Prop) (x2 : type686 a0) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 (@IMAGE a0 (a0 -> Prop) x0 x1)) -> x2 y0.
Definition term196 (a0 : Type') (x0 : a0 -> Prop) := (((~ (forall y0 : a0, forall y1 : a0, ((x0 y0) /\ ((x0 y1) /\ (forall y2 : a0, (y2 = y0) = (y2 = y1)))) -> y0 = y1)) -> False) -> (~ (forall y0 : a0, forall y1 : a0, ((x0 y0) /\ ((x0 y1) /\ (forall y2 : a0, (y2 = y0) = (y2 = y1)))) -> y0 = y1)) -> False) -> (~ (forall y0 : a0, forall y1 : a0, ((x0 y0) /\ ((x0 y1) /\ (forall y2 : a0, (y2 = y0) = (y2 = y1)))) -> y0 = y1)) -> False.
Definition term45 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@SUBSET a0 y0 x0) -> @FINITE a0 y0.
Definition term202 (a0 : Type') := forall y0 : a0 -> Prop, (~ (forall y1 : a0, forall y2 : a0, ((y0 y1) /\ ((y0 y2) /\ (forall y3 : a0, (y3 = y1) = (y3 = y2)))) -> y1 = y2)) -> False.
Definition term30 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) -> x2.
Definition term123 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) := forall y0 : Prop, forall y1 : Prop, ((@IN a0 x1 ((fun y2 : a0 => @INSERT a0 y2 (@EMPTY a0)) x0)) = y0) -> (y0 -> (@IN a0 x1 x2) = y1) -> ((@IN a0 x1 ((fun y2 : a0 => @INSERT a0 y2 (@EMPTY a0)) x0)) -> @IN a0 x1 x2) = (y0 -> y1).
Definition term94 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : Prop, forall y1 : Prop, ((@IN a0 x0 x1) = y0) -> (y0 -> (@IN (a0 -> Prop) ((fun y2 : a0 => @INSERT a0 y2 (@EMPTY a0)) x0) (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 (@SUBSET a0 y3 x1) y3))) = y1) -> ((@IN a0 x0 x1) -> @IN (a0 -> Prop) ((fun y2 : a0 => @INSERT a0 y2 (@EMPTY a0)) x0) (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 (@SUBSET a0 y3 x1) y3))) = (y0 -> y1).
Definition term93 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term85 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := imp (@IN a0 x0 x1).
Definition term117 (a0 : Type') (x0 : a0 -> Prop) := @GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => @SUBSET a0 y2 x0) y1) y1).
Definition term56 (a0 : Type') (x0 : a0 -> Prop) := @GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x0) y1).
Definition term205 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (x0 = x1).
Definition term179 (a0 : Type') (x0 : a0) (x1 : a0) := or (x0 = x1).
Definition term41 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@SUBSET a0 y0 y1) -> @FINITE a0 y0.
Definition term40 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y1) /\ (@SUBSET a0 y0 y1)) -> @FINITE a0 y0.
Definition term0 (a0 : Type') (a1 : Type') := forall y0 : a0 -> a1, forall y1 : a0 -> Prop, (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ ((y0 y2) = (y0 y3)))) -> y2 = y3) -> (@FINITE a1 (@IMAGE a0 a1 y0 y1)) = (@FINITE a0 y1).
Definition term105 (a0 : Type') (x0 : a0) := (fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0.
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := (forall y0 : type686 a0, (@SUBSET (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 x0) y2))) -> @FINITE (a0 -> Prop) y0) -> @FINITE (a0 -> Prop) x1.
Definition term24 (a0 : Type') (a1 : Type') (x0 : a1 -> a0) (x1 : a1 -> Prop) (x2 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@IMAGE a1 a0 x0 x1)) -> x2 y0.
Definition term99 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : Prop) := ((@IN a0 x0 x1) = (@IN a0 x0 x1)) -> ((@IN a0 x0 x1) -> (@IN (a0 -> Prop) ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x1) y1))) = x2) -> ((@IN a0 x0 x1) -> @IN (a0 -> Prop) ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x1) y1))) = ((@IN a0 x0 x1) -> x2).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (x0 y2) y2))) = (x0 y0)) x1.
Definition term127 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((@IN a0 x1 ((fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) x0)) = x3) -> (x3 -> (@IN a0 x1 x2) = y0) -> ((@IN a0 x1 ((fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) x0)) -> @IN a0 x1 x2) = (x3 -> y0)) x4.
Definition term247 (a0 : Type') (x0 : a0) (x1 : a0) := imp (x0 = x1).
Definition term181 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop (x0 = x1).
Definition term134 (a0 : Type') (x0 : a0) := @eq (a0 -> Prop) ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0).
Definition term231 (a0 : Type') (x0 : a0) (x1 : a0) := and (forall y0 : a0, (y0 = x0) \/ (~ (y0 = x1))).
Definition term253 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (forall y1 : a0, forall y2 : a0, ((y0 y1) /\ ((y0 y2) /\ (forall y3 : a0, (y3 = y1) = (y3 = y2)))) -> y1 = y2)) -> False) x0.
Definition term102 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN (a0 -> Prop) ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => @SUBSET a0 y2 x1) y1) y1)).
Definition term84 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN (a0 -> Prop) ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x1) y1)).
Definition term249 (a0 : Type') (x0 : a0) (x1 : a0) := (x0 = x0) -> x0 = x1.
Definition term120 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @eq Prop (@IN (a0 -> Prop) ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x1) y1))).
Definition term119 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @eq Prop (@IN (a0 -> Prop) ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 ((fun y2 : a0 -> Prop => @SUBSET a0 y2 x1) y1) y1))).
Definition term25 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : a1 -> a0) := forall y0 : a1, (@IN a1 y0 x0) -> x1 (x2 y0).
Definition term80 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 (@IMAGE a0 (a0 -> Prop) (fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) x0)) -> @IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 x0) y2)).
Definition term221 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := (fun y0 : a0 => (~ (y0 = x0)) \/ (y0 = x1)) x2.
Definition term210 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (x0 x1) /\ ((x0 x2) /\ (forall y0 : a0, ((y0 = x1) \/ (~ (y0 = x2))) /\ ((~ (y0 = x1)) \/ (y0 = x2)))).
Definition term185 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := (x0 x1) /\ ((x0 x2) /\ (forall y0 : a0, (y0 = x1) = (y0 = x2))).
Definition term122 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 ((fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) x0)) -> @IN a0 y0 x1.
Definition term178 (a0 : Type') (x0 : a0) (x1 : a0) := (x1 = x0) \/ (@IN a0 x1 (@EMPTY a0)).
Definition term15 (a0 : Type') (x0 : a0) (x1 : a0) := @IN a0 x0 (@INSERT a0 x1 (@EMPTY a0)).
Definition term72 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => @IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 x0) y2)).
Definition term191 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, forall y1 : a0, ((x0 y0) /\ ((x0 y1) /\ (forall y2 : a0, (y2 = y0) = (y2 = y1)))) -> y0 = y1.
Definition term174 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x0) /\ ((@IN a0 y1 x0) /\ (forall y2 : a0, (@IN a0 y2 (@INSERT a0 y0 (@EMPTY a0))) = (@IN a0 y2 (@INSERT a0 y1 (@EMPTY a0)))))) -> y0 = y1.
Definition term173 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x0) /\ ((@IN a0 y1 x0) /\ (((fun y2 : a0 => @INSERT a0 y2 (@EMPTY a0)) y0) = ((fun y2 : a0 => @INSERT a0 y2 (@EMPTY a0)) y1)))) -> y0 = y1.
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a0 -> a1) := forall y0 : a0, forall y1 : a0, ((@IN a0 y0 x0) /\ ((@IN a0 y1 x0) /\ ((x1 y0) = (x1 y1)))) -> y0 = y1.
Definition term207 (a0 : Type') (x0 : a0) (x1 : a0) := fun y0 : a0 => ((y0 = x0) \/ (~ (y0 = x1))) /\ ((~ (y0 = x0)) \/ (y0 = x1)).
Definition term104 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => @SUBSET a0 y0 x0.
Definition term238 (a0 : Type') (x0 : a0) := (~ (x0 = x0)) -> x0 = x0.
Definition term186 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := imp ((x0 x1) /\ ((x0 x2) /\ (forall y0 : a0, (y0 = x1) = (y0 = x2)))).
Definition term23 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> a0) (x2 : a1 -> Prop) := (fun y0 : a1 -> Prop => (forall y1 : a0, (@IN a0 y1 (@IMAGE a1 a0 x1 y0)) -> x0 y1) = (forall y1 : a1, (@IN a1 y1 y0) -> x0 (x1 y1))) x2.
Definition term152 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : a0, (@IN a0 y0 ((fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) x0)) = (@IN a0 y0 ((fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) x1)).
Definition term121 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @SUBSET a0 ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0) x1.
Definition term13 (a0 : Type') (x0 : a0) := forall y0 : a0, (@IN a0 x0 (@INSERT a0 y0 (@EMPTY a0))) = (x0 = y0).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> Prop) := (forall y0 : a0 -> a1, forall y1 : a0 -> Prop, (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ ((y0 y2) = (y0 y3)))) -> y2 = y3) -> (@FINITE a1 (@IMAGE a0 a1 y0 y1)) = (@FINITE a0 y1)) -> (@FINITE a1 (@IMAGE a0 a1 x0 x1)) = (@FINITE a0 x1).
Definition term167 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := fun y0 : a0 => ((@IN a0 x1 x0) /\ ((@IN a0 y0 x0) /\ (((fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) x1) = ((fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) y0)))) -> x1 = y0.
Definition term101 (a0 : Type') (x0 : a0 -> Prop) (x1 : type686 a0) := @IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (x1 y1) y1)).
Definition term75 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x1) y1)).
Definition term140 (a0 : Type') (x0 : a0) (x1 : a0) := (x0 = x1) -> True.
Definition term194 (a0 : Type') (x0 : a0 -> Prop) := ~ (forall y0 : a0, forall y1 : a0, ((x0 y0) /\ ((x0 y1) /\ (forall y2 : a0, (y2 = y0) = (y2 = y1)))) -> y0 = y1).
Definition term110 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 (@SUBSET a0 x2 x1) x2.
Definition term112 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => @SETSPEC (a0 -> Prop) x0 (@SUBSET a0 y0 x1) y0.
Definition term29 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) -> @IN a0 y0 x1.
Definition term165 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ((@IN a0 x1 x0) /\ ((@IN a0 x2 x0) /\ (((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x1) = ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x2)))) -> x1 = x2.
Definition term135 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) (x3 : Prop) := ((@IN a0 x1 ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x2)) = (x1 = x2)) -> ((x1 = x2) -> (@IN a0 x1 x0) = x3) -> ((@IN a0 x1 ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x2)) -> @IN a0 x1 x0) = ((x1 = x2) -> x3).
Definition term76 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := imp (@IN (a0 -> Prop) x0 (@IMAGE a0 (a0 -> Prop) (fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x1)).
Definition term203 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, forall y2 : a0, ((y0 y1) /\ ((y0 y2) /\ (forall y3 : a0, (y3 = y1) = (y3 = y2)))) -> y1 = y2.
Definition term86 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (@IN a0 x1 x0) -> (fun y0 : a0 -> Prop => @IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 x0) y2))) ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x1).
Definition term71 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) -> (fun y1 : a0 -> Prop => @IN (a0 -> Prop) y1 (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 (@SUBSET a0 y3 x0) y3))) ((fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) y0).
Definition term73 (a0 : Type') := fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0).
Definition term89 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 x0) -> @IN (a0 -> Prop) ((fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) y0) (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 x0) y2)).
Definition term211 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) /\ (x1 y0).
Definition term48 (a0 : Type') := (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@SUBSET a0 y0 y1) -> @FINITE a0 y0) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> forall y1 : a0 -> Prop, (@SUBSET a0 y1 y0) -> @FINITE a0 y1.
Definition term214 (a0 : Type') (x0 : a0) (x1 : a0) := (forall y0 : a0, (fun y1 : a0 => (y1 = x0) \/ (~ (y1 = x1))) y0) /\ (forall y0 : a0, (fun y1 : a0 => (~ (y1 = x0)) \/ (y1 = x1)) y0).
Definition term108 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @SETSPEC (a0 -> Prop) x0 (@SUBSET a0 x1 x2).
Definition term197 (a0 : Type') (x0 : a0 -> Prop) := (((~ (forall y0 : a0, forall y1 : a0, ((x0 y0) /\ ((x0 y1) /\ (forall y2 : a0, (y2 = y0) = (y2 = y1)))) -> y0 = y1)) -> False) -> (~ (forall y0 : a0, forall y1 : a0, ((x0 y0) /\ ((x0 y1) /\ (forall y2 : a0, (y2 = y0) = (y2 = y1)))) -> y0 = y1)) -> False) -> ((~ (forall y0 : a0, forall y1 : a0, ((x0 y0) /\ ((x0 y1) /\ (forall y2 : a0, (y2 = y0) = (y2 = y1)))) -> y0 = y1)) -> False) -> (~ (forall y0 : a0, forall y1 : a0, ((x0 y0) /\ ((x0 y1) /\ (forall y2 : a0, (y2 = y0) = (y2 = y1)))) -> y0 = y1)) -> False.
Definition term43 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@SUBSET a0 x0 y0) -> @FINITE a0 x0) x1.
Definition term10 (x0 : Prop) (x1 : Prop) := ((x0 = x1) -> x0 -> x1) -> x0 -> x1.
Definition term200 (a0 : Type') := fun y0 : a0 -> Prop => (~ (forall y1 : a0, forall y2 : a0, ((y0 y1) /\ ((y0 y2) /\ (forall y3 : a0, (y3 = y1) = (y3 = y2)))) -> y1 = y2)) -> False.
Definition term225 (a0 : Type') (x0 : a0) (x1 : a0) := @eq Prop (forall y0 : a0, ((fun y1 : a0 => (y1 = x0) \/ (~ (y1 = x1))) y0) /\ ((fun y1 : a0 => (~ (y1 = x0)) \/ (y1 = x1)) y0)).
Definition term255 (a0 : Type') (x0 : a0 -> Prop) := (@FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x0) y1))) -> @FINITE a0 x0.
Definition term223 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := ((fun y0 : a0 => (y0 = x0) \/ (~ (y0 = x1))) x2) /\ ((fun y0 : a0 => (~ (y0 = x0)) \/ (y0 = x1)) x2).
Definition term166 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0) := ((@IN a0 x1 x0) /\ ((@IN a0 x2 x0) /\ (forall y0 : a0, (@IN a0 y0 (@INSERT a0 x1 (@EMPTY a0))) = (@IN a0 y0 (@INSERT a0 x2 (@EMPTY a0)))))) -> x1 = x2.
Definition term28 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@SUBSET a0 x0 y0) = (forall y1 : a0, (@IN a0 y1 x0) -> @IN a0 y1 y0)) x1.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> Prop, (forall y2 : a0, forall y3 : a0, ((@IN a0 y2 y1) /\ ((@IN a0 y3 y1) /\ ((y0 y2) = (y0 y3)))) -> y2 = y3) -> (@FINITE a1 (@IMAGE a0 a1 y0 y1)) = (@FINITE a0 y1)) x0.
Definition term257 (a0 : Type') := forall y0 : a0 -> Prop, (@FINITE (a0 -> Prop) (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 y0) y2))) = (@FINITE a0 y0).
Definition term100 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : Prop) := ((@IN a0 x0 x1) -> (@IN (a0 -> Prop) ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x1) y1))) = x2) -> ((@IN a0 x0 x1) -> @IN (a0 -> Prop) ((fun y0 : a0 => @INSERT a0 y0 (@EMPTY a0)) x0) (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a0 -> Prop, @SETSPEC (a0 -> Prop) y0 (@SUBSET a0 y1 x1) y1))) = ((@IN a0 x0 x1) -> x2).
Definition term95 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@IN a0 x0 x1) = y0) -> (y0 -> (@IN (a0 -> Prop) ((fun y2 : a0 => @INSERT a0 y2 (@EMPTY a0)) x0) (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 (@SUBSET a0 y3 x1) y3))) = y1) -> ((@IN a0 x0 x1) -> @IN (a0 -> Prop) ((fun y2 : a0 => @INSERT a0 y2 (@EMPTY a0)) x0) (@GSPEC (a0 -> Prop) (fun y2 : a0 -> Prop => exists y3 : a0 -> Prop, @SETSPEC (a0 -> Prop) y2 (@SUBSET a0 y3 x1) y3))) = (y0 -> y1)) x2.
Definition term67 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 (@IMAGE a0 (a0 -> Prop) (fun y1 : a0 => @INSERT a0 y1 (@EMPTY a0)) x0)) -> @IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a0 -> Prop, @SETSPEC (a0 -> Prop) y1 (@SUBSET a0 y2 x0) y2)).
Definition term220 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := and ((x1 = x0) \/ (~ (x1 = x2))).
Definition term16 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 (y0 y3) y3))) = (y0 y1).
Definition term245 (a0 : Type') (x0 : a0) (x1 : a0) := ~ (~ (x0 = x1)).
Definition term27 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (@SUBSET a0 x0 y0) = (forall y1 : a0, (@IN a0 y1 x0) -> @IN a0 y1 y0).
Definition term241 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := @eq Prop ((~ (x1 = x0)) \/ (x1 = x2)).
Definition term232 (a0 : Type') (x0 : a0) (x1 : a0) := fun y0 : a0 => (fun y1 : a0 => (~ (y1 = x0)) \/ (y1 = x1)) y0.
Definition term44 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@SUBSET a0 x1 x0) -> @FINITE a0 x1.
Definition term246 (a0 : Type') (x0 : a0) (x1 : a0) := imp (~ (~ (x0 = x1))).
