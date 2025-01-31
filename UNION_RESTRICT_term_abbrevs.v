Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term54 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ (x2 x3)) x3.
Definition term114 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((((x0 x3) \/ (x1 x3)) /\ (x2 x3)) /\ (~ (((x0 x3) /\ (x2 x3)) \/ ((x1 x3) /\ (x2 x3))))) \/ ((~ (((x0 x3) \/ (x1 x3)) /\ (x2 x3))) /\ (((x0 x3) /\ (x2 x3)) \/ ((x1 x3) /\ (x2 x3)))).
Definition term119 := (~ False) -> False.
Definition term102 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ ((x0 x3) /\ (x2 x3))) /\ (~ ((x1 x3) /\ (x2 x3))).
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) := (@IN a0 x1 x0) \/ (@IN a0 x1 x2).
Definition term87 (x0 : Prop) := ~ (~ x0).
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (fun y0 : a0 => (@IN a0 y0 (@UNION a0 x0 x1)) /\ (x2 y0)) x3.
Definition term111 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (((x0 x3) \/ (x1 x3)) /\ (x2 x3)) /\ (((~ (x0 x3)) \/ (~ (x2 x3))) /\ ((~ (x1 x3)) \/ (~ (x2 x3)))).
Definition term2 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @UNION a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (x2 y1)) y1)) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (x2 y1)) y1)).
Definition term90 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x0 x2) \/ (x1 x2)).
Definition term67 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) /\ (x1 x2).
Definition term92 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := ~ (x0 x1).
Definition term57 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := exists y0 : a0, @SETSPEC a0 x0 ((fun y1 : a0 => (@IN a0 y1 x1) /\ (x2 y1)) y0) y0.
Definition term27 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := exists y0 : a0, @SETSPEC a0 x0 ((fun y1 : a0 => (@IN a0 y1 (@UNION a0 x1 x2)) /\ (x3 y1)) y0) y0.
Definition term79 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y1 y3) \/ (y2 y3)) /\ (y0 y3)) = (((y1 y3) /\ (y0 y3)) \/ ((y2 y3) /\ (y0 y3))).
Definition term77 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, (((y0 y2) \/ (y1 y2)) /\ (x0 y2)) = (((y0 y2) /\ (x0 y2)) \/ ((y1 y2) /\ (x0 y2))).
Definition term15 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (@IN a0 y3 (@GSPEC a0 (fun y4 : a0 => exists y5 : a0, @SETSPEC a0 y4 ((@IN a0 y5 (@UNION a0 y1 y2)) /\ (y0 y5)) y5))) = (@IN a0 y3 (@UNION a0 (@GSPEC a0 (fun y4 : a0 => exists y5 : a0, @SETSPEC a0 y4 ((@IN a0 y5 y1) /\ (y0 y5)) y5)) (@GSPEC a0 (fun y4 : a0 => exists y5 : a0, @SETSPEC a0 y4 ((@IN a0 y5 y2) /\ (y0 y5)) y5)))).
Definition term14 (a0 : Type') := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 (@UNION a0 y1 y2)) /\ (y0 y4)) y4)) = (@UNION a0 (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 y1) /\ (y0 y4)) y4)) (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 y2) /\ (y0 y4)) y4))).
Definition term11 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0, (@IN a0 y2 (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 (@UNION a0 y0 y1)) /\ (x0 y4)) y4))) = (@IN a0 y2 (@UNION a0 (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 y0) /\ (x0 y4)) y4)) (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 y1) /\ (x0 y4)) y4)))).
Definition term80 (x0 : Prop) := (~ x0) -> False.
Definition term88 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ ((((x0 x3) \/ (x1 x3)) /\ (x2 x3)) = (((x0 x3) /\ (x2 x3)) \/ ((x1 x3) /\ (x2 x3))))) -> False.
Definition term20 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (@IN a0 x3 (@UNION a0 x0 x1)) /\ (x2 x3).
Definition term52 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @SETSPEC a0 x0 ((@IN a0 x3 x1) /\ (x2 x3)).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 (@UNION a0 x0 y0)) /\ (x1 y2)) y2)) = (@UNION a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (x1 y2)) y2)) (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 y0) /\ (x1 y2)) y2))).
Definition term49 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 x0) /\ (x1 y0).
Definition term109 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := and (((x0 x3) \/ (x1 x3)) /\ (x2 x3)).
Definition term0 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term82 (a0 : Type') := ~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y1 y3) \/ (y2 y3)) /\ (y0 y3)) = (((y1 y3) /\ (y0 y3)) \/ ((y2 y3) /\ (y0 y3)))).
Definition term117 (x0 : Prop) := (~ x0) -> x0.
Definition term105 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := and (~ (((x0 x3) \/ (x1 x3)) /\ (x2 x3))).
Definition term104 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ~ (((x0 x3) /\ (x2 x3)) \/ ((x1 x3) /\ (x2 x3))).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 (@UNION a0 y0 y1)) /\ (x0 y3)) y3)) = (@UNION a0 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y0) /\ (x0 y3)) y3)) (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y1) /\ (x0 y3)) y3))).
Definition term45 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := (@IN a0 x1 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (x3 y1)) y1))) \/ (@IN a0 x1 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x2) /\ (x3 y1)) y1))).
Definition term103 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((~ (x0 x3)) \/ (~ (x2 x3))) /\ ((~ (x1 x3)) \/ (~ (x2 x3))).
Definition term59 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x0) /\ (x1 y2)) y1) y1.
Definition term29 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 (@UNION a0 x0 x1)) /\ (x2 y2)) y1) y1.
Definition term40 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := and (@IN a0 x0 (@UNION a0 x1 x2)).
Definition term108 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (((~ (x0 x3)) /\ (~ (x1 x3))) \/ (~ (x2 x3))) /\ (((x0 x3) /\ (x2 x3)) \/ ((x1 x3) /\ (x2 x3))).
Definition term6 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0 -> Prop, (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 (@UNION a0 x0 y0)) /\ (x1 y2)) y2)) = (@UNION a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (x1 y2)) y2)) (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 y0) /\ (x1 y2)) y2))).
Definition term35 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@UNION a0 x1 x2).
Definition term26 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := fun y0 : a0 => @SETSPEC a0 x0 ((@IN a0 y0 (@UNION a0 x1 x2)) /\ (x3 y0)) y0.
Definition term101 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := and ((~ (x0 x2)) \/ (~ (x1 x2))).
Definition term94 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or ((~ (x0 x2)) /\ (~ (x1 x2))).
Definition term62 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (x2 y1)) y1)).
Definition term47 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x1) /\ (x2 y2)) y1) y1)).
Definition term32 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 (@UNION a0 x1 x2)) /\ (x3 y1)) y1)).
Definition term17 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 (@UNION a0 x1 x2)) /\ (x3 y2)) y1) y1)).
Definition term16 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x1 y1) y1)).
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (fun y0 : a0 => (@IN a0 y0 x0) /\ (x1 y0)) x2.
Definition term65 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := and (@IN a0 x0 x1).
Definition term64 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (x2 y1)) y1))).
Definition term63 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x1) /\ (x2 y2)) y1) y1))).
Definition term34 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 (@UNION a0 x1 x2)) /\ (x3 y1)) y1))).
Definition term33 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 (@UNION a0 x1 x2)) /\ (x3 y2)) y1) y1))).
Definition term44 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := @IN a0 x0 (@UNION a0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (x3 y1)) y1)) (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x2) /\ (x3 y1)) y1))).
Definition term115 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((((x0 x3) \/ (x1 x3)) /\ (x2 x3)) /\ (((~ (x0 x3)) \/ (~ (x2 x3))) /\ ((~ (x1 x3)) \/ (~ (x2 x3))))) \/ ((((~ (x0 x3)) /\ (~ (x1 x3))) \/ (~ (x2 x3))) /\ (((x0 x3) /\ (x2 x3)) \/ ((x1 x3) /\ (x2 x3)))).
Definition term113 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := or ((((x0 x3) \/ (x1 x3)) /\ (x2 x3)) /\ (((~ (x0 x3)) \/ (~ (x2 x3))) /\ ((~ (x1 x3)) \/ (~ (x2 x3))))).
Definition term69 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or ((x0 x2) /\ (x1 x2)).
Definition term83 (a0 : Type') := ((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y1 y3) \/ (y2 y3)) /\ (y0 y3)) = (((y1 y3) /\ (y0 y3)) \/ ((y2 y3) /\ (y0 y3))))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y1 y3) \/ (y2 y3)) /\ (y0 y3)) = (((y1 y3) /\ (y0 y3)) \/ ((y2 y3) /\ (y0 y3))))) -> False.
Definition term42 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((x0 x3) \/ (x1 x3)) /\ (x2 x3).
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 x0) /\ (x1 y2)) y1) y1).
Definition term46 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (x1 y1)) y1).
Definition term31 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => (@IN a0 y2 (@UNION a0 x0 x1)) /\ (x2 y2)) y1) y1).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 (@UNION a0 x0 x1)) /\ (x2 y1)) y1).
Definition term74 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, (((x0 y1) \/ (y0 y1)) /\ (x1 y1)) = (((x0 y1) /\ (x1 y1)) \/ ((y0 y1) /\ (x1 y1))).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 (@UNION a0 x0 y0)) /\ (x1 y3)) y3))) = (@IN a0 y1 (@UNION a0 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 x0) /\ (x1 y3)) y3)) (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y0) /\ (x1 y3)) y3)))).
Definition term73 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := forall y0 : a0, (((x0 y0) \/ (x1 y0)) /\ (x2 y0)) = (((x0 y0) /\ (x2 y0)) \/ ((x1 y0) /\ (x2 y0))).
Definition term66 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := and (x0 x1).
Definition term55 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => @SETSPEC a0 x0 ((fun y1 : a0 => (@IN a0 y1 x1) /\ (x2 y1)) y0) y0.
Definition term25 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := fun y0 : a0 => @SETSPEC a0 x0 ((fun y1 : a0 => (@IN a0 y1 (@UNION a0 x1 x2)) /\ (x3 y1)) y0) y0.
Definition term95 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ ((x0 x3) \/ (x1 x3))) \/ (~ (x2 x3)).
Definition term58 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := exists y0 : a0, @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ (x2 y0)) y0.
Definition term28 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := exists y0 : a0, @SETSPEC a0 x0 ((@IN a0 y0 (@UNION a0 x1 x2)) /\ (x3 y0)) y0.
Definition term91 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x2)) /\ (~ (x1 x2)).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 (@UNION a0 x0 x1)) /\ (x2 y2)) y2))) = (@IN a0 y0 (@UNION a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (x2 y2)) y2)) (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x1) /\ (x2 y2)) y2)))).
Definition term86 (a0 : Type') := ~ (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y1 y3) \/ (y2 y3)) /\ (y0 y3)) = (((y1 y3) /\ (y0 y3)) \/ ((y2 y3) /\ (y0 y3))))).
Definition term81 (a0 : Type') := (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y1 y3) \/ (y2 y3)) /\ (y0 y3)) = (((y1 y3) /\ (y0 y3)) \/ ((y2 y3) /\ (y0 y3))))) -> False.
Definition term43 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @eq Prop (((x0 x3) \/ (x1 x3)) /\ (x2 x3)).
Definition term71 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 (@UNION a0 x0 x1)) /\ (x2 y2)) y2))) = (@IN a0 y0 (@UNION a0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x0) /\ (x2 y2)) y2)) (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 ((@IN a0 y2 x1) /\ (x2 y2)) y2)))).
Definition term50 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (@IN a0 x2 x0) /\ (x1 x2).
Definition term84 (a0 : Type') := (((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y1 y3) \/ (y2 y3)) /\ (y0 y3)) = (((y1 y3) /\ (y0 y3)) \/ ((y2 y3) /\ (y0 y3))))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y1 y3) \/ (y2 y3)) /\ (y0 y3)) = (((y1 y3) /\ (y0 y3)) \/ ((y2 y3) /\ (y0 y3))))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y1 y3) \/ (y2 y3)) /\ (y0 y3)) = (((y1 y3) /\ (y0 y3)) \/ ((y2 y3) /\ (y0 y3))))) -> False.
Definition term60 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x0) /\ (x1 y1)) y1.
Definition term30 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 (@UNION a0 x0 x1)) /\ (x2 y1)) y1.
Definition term10 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 (@UNION a0 y0 y1)) /\ (x0 y3)) y3)) = (@UNION a0 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y0) /\ (x0 y3)) y3)) (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y1) /\ (x0 y3)) y3))).
Definition term41 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := and ((x0 x2) \/ (x1 x2)).
Definition term39 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (x0 x2) \/ (x1 x2).
Definition term23 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> Prop) (x4 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => (@IN a0 y0 (@UNION a0 x1 x2)) /\ (x3 y0)) x4) x4.
Definition term93 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := or (~ ((x0 x2) \/ (x1 x2))).
Definition term99 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := (~ (x0 x2)) \/ (~ (x1 x2)).
Definition term56 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => @SETSPEC a0 x0 ((@IN a0 y0 x1) /\ (x2 y0)) y0.
Definition term96 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((~ (x0 x3)) /\ (~ (x1 x3))) \/ (~ (x2 x3)).
Definition term22 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> Prop) (x4 : a0) := @SETSPEC a0 x0 ((@IN a0 x4 (@UNION a0 x1 x2)) /\ (x3 x4)).
Definition term112 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := or ((((x0 x3) \/ (x1 x3)) /\ (x2 x3)) /\ (~ (((x0 x3) /\ (x2 x3)) \/ ((x1 x3) /\ (x2 x3))))).
Definition term118 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (x0 x1) -> False.
Definition term110 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (((x0 x3) \/ (x1 x3)) /\ (x2 x3)) /\ (~ (((x0 x3) /\ (x2 x3)) \/ ((x1 x3) /\ (x2 x3)))).
Definition term68 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := or (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((@IN a0 y1 x1) /\ (x2 y1)) y1))).
Definition term78 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y1 y3) \/ (y2 y3)) /\ (y0 y3)) = (((y1 y3) /\ (y0 y3)) \/ ((y2 y3) /\ (y0 y3))).
Definition term76 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, (((y0 y2) \/ (y1 y2)) /\ (x0 y2)) = (((y0 y2) /\ (x0 y2)) \/ ((y1 y2) /\ (x0 y2))).
Definition term13 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (@IN a0 y3 (@GSPEC a0 (fun y4 : a0 => exists y5 : a0, @SETSPEC a0 y4 ((@IN a0 y5 (@UNION a0 y1 y2)) /\ (y0 y5)) y5))) = (@IN a0 y3 (@UNION a0 (@GSPEC a0 (fun y4 : a0 => exists y5 : a0, @SETSPEC a0 y4 ((@IN a0 y5 y1) /\ (y0 y5)) y5)) (@GSPEC a0 (fun y4 : a0 => exists y5 : a0, @SETSPEC a0 y4 ((@IN a0 y5 y2) /\ (y0 y5)) y5)))).
Definition term12 (a0 : Type') := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 (@UNION a0 y1 y2)) /\ (y0 y4)) y4)) = (@UNION a0 (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 y1) /\ (y0 y4)) y4)) (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 y2) /\ (y0 y4)) y4))).
Definition term9 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, forall y2 : a0, (@IN a0 y2 (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 (@UNION a0 y0 y1)) /\ (x0 y4)) y4))) = (@IN a0 y2 (@UNION a0 (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 y0) /\ (x0 y4)) y4)) (@GSPEC a0 (fun y3 : a0 => exists y4 : a0, @SETSPEC a0 y3 ((@IN a0 y4 y1) /\ (x0 y4)) y4)))).
Definition term21 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> Prop) (x4 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => (@IN a0 y0 (@UNION a0 x1 x2)) /\ (x3 y0)) x4).
Definition term107 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := (~ (((x0 x3) \/ (x1 x3)) /\ (x2 x3))) /\ (((x0 x3) /\ (x2 x3)) \/ ((x1 x3) /\ (x2 x3))).
Definition term85 (a0 : Type') := (((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y1 y3) \/ (y2 y3)) /\ (y0 y3)) = (((y1 y3) /\ (y0 y3)) \/ ((y2 y3) /\ (y0 y3))))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y1 y3) \/ (y2 y3)) /\ (y0 y3)) = (((y1 y3) /\ (y0 y3)) \/ ((y2 y3) /\ (y0 y3))))) -> False) -> ((~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y1 y3) \/ (y2 y3)) /\ (y0 y3)) = (((y1 y3) /\ (y0 y3)) \/ ((y2 y3) /\ (y0 y3))))) -> False) -> (~ (forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, forall y3 : a0, (((y1 y3) \/ (y2 y3)) /\ (y0 y3)) = (((y1 y3) /\ (y0 y3)) \/ ((y2 y3) /\ (y0 y3))))) -> False.
Definition term53 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => (@IN a0 y0 x1) /\ (x2 y0)) x3) x3.
Definition term37 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := or (@IN a0 x0 x1).
Definition term100 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := and (~ ((x0 x2) /\ (x1 x2))).
Definition term72 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => (((x0 y0) \/ (x1 y0)) /\ (x2 y0)) = (((x0 y0) /\ (x2 y0)) \/ ((x1 y0) /\ (x2 y0))).
Definition term116 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (~ (x0 x1)) -> x0 x1.
Definition term98 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0) := ~ ((x0 x2) /\ (x1 x2)).
Definition term75 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, (((x0 y1) \/ (y0 y1)) /\ (x1 y1)) = (((x0 y1) /\ (x1 y1)) \/ ((y0 y1) /\ (x1 y1))).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0 -> Prop, forall y1 : a0, (@IN a0 y1 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 (@UNION a0 x0 y0)) /\ (x1 y3)) y3))) = (@IN a0 y1 (@UNION a0 (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 x0) /\ (x1 y3)) y3)) (@GSPEC a0 (fun y2 : a0 => exists y3 : a0, @SETSPEC a0 y2 ((@IN a0 y3 y0) /\ (x1 y3)) y3)))).
Definition term89 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ~ ((((x0 x3) \/ (x1 x3)) /\ (x2 x3)) = (((x0 x3) /\ (x2 x3)) \/ ((x1 x3) /\ (x2 x3)))).
Definition term97 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ~ (((x0 x3) \/ (x1 x3)) /\ (x2 x3)).
Definition term70 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := ((x0 x3) /\ (x2 x3)) \/ ((x1 x3) /\ (x2 x3)).
Definition term106 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := and (((~ (x0 x3)) /\ (~ (x1 x3))) \/ (~ (x2 x3))).
Definition term24 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0 -> Prop) (x4 : a0) := @SETSPEC a0 x0 ((@IN a0 x4 (@UNION a0 x1 x2)) /\ (x3 x4)) x4.
Definition term38 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := or (x0 x1).
Definition term19 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> Prop) := fun y0 : a0 => (@IN a0 y0 (@UNION a0 x0 x1)) /\ (x2 y0).
Definition term51 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> Prop) (x3 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => (@IN a0 y0 x1) /\ (x2 y0)) x3).
