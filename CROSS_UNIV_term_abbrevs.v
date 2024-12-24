Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term26 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := @IN (prod a0 a1) x0 (@CROSS a1 a0 (@UNIV a0) (@UNIV a1)).
Definition term35 (a0 : Type') (a1 : Type') (x0 : a0) := forall y0 : a1, (fun y1 : prod a0 a1 => (@IN (prod a0 a1) y1 (@CROSS a1 a0 (@UNIV a0) (@UNIV a1))) = (@IN (prod a0 a1) y1 (@UNIV (prod a0 a1)))) (@pair a0 a1 x0 y0).
Definition term23 (a0 : Type') (a1 : Type') := forall y0 : a0, forall y1 : a1, (fun y2 : prod a0 a1 => (@IN (prod a0 a1) y2 (@CROSS a1 a0 (@UNIV a0) (@UNIV a1))) = (@IN (prod a0 a1) y2 (@UNIV (prod a0 a1)))) (@pair a0 a1 y0 y1).
Definition term20 (a0 : Type') (a1 : Type') (x0 : type1210 a0 a1) := forall y0 : prod a0 a1, x0 y0.
Definition term2 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : prod a1 a0, x0 y0.
Definition term61 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @IN (prod a0 a1) (@pair a0 a1 x0 x1) (@GSPEC (prod a0 a1) (fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, @SETSPEC (prod a0 a1) y0 ((fun y3 : a0 => fun y4 : a1 => True) y1 y2) (@pair a0 a1 y1 y2))).
Definition term60 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : type1413 a0 a1) := @IN (prod a0 a1) (@pair a0 a1 x0 x1) (@GSPEC (prod a0 a1) (fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, @SETSPEC (prod a0 a1) y0 (x2 y1 y2) (@pair a0 a1 y1 y2))).
Definition term59 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @IN (prod a0 a1) (@pair a0 a1 x0 x1) (@GSPEC (prod a0 a1) (fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, @SETSPEC (prod a0 a1) y0 True (@pair a0 a1 y1 y2))).
Definition term79 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term51 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := fun y0 : a0 => exists y1 : a1, @SETSPEC (prod a0 a1) x0 ((@IN a0 y0 (@UNIV a0)) /\ (@IN a1 y1 (@UNIV a1))) (@pair a0 a1 y0 y1).
Definition term4 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := (fun y0 : type1470 a0 a1 => forall y1 : a1, forall y2 : a0, (@IN (prod a1 a0) (@pair a1 a0 y1 y2) (@GSPEC (prod a1 a0) (fun y3 : prod a1 a0 => exists y4 : a1, exists y5 : a0, @SETSPEC (prod a1 a0) y3 (y0 y4 y5) (@pair a1 a0 y4 y5)))) = (y0 y1 y2)) x0.
Definition term78 (a0 : Type') := forall y0 : a0, True.
Definition term47 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : a0) := fun y0 : a1 => @SETSPEC (prod a0 a1) x0 ((@IN a0 x1 (@UNIV a0)) /\ (@IN a1 y0 (@UNIV a1))) (@pair a0 a1 x1 y0).
Definition term72 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := exists y0 : a0, exists y1 : a1, @SETSPEC (prod a0 a1) x0 ((fun y2 : a0 => fun y3 : a1 => True) y0 y1) (@pair a0 a1 y0 y1).
Definition term54 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := exists y0 : a0, exists y1 : a1, @SETSPEC (prod a0 a1) x0 True (@pair a0 a1 y0 y1).
Definition term53 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := exists y0 : a0, exists y1 : a1, @SETSPEC (prod a0 a1) x0 ((@IN a0 y0 (@UNIV a0)) /\ (@IN a1 y1 (@UNIV a1))) (@pair a0 a1 y0 y1).
Definition term77 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @eq Prop (@IN (prod a0 a1) (@pair a0 a1 x0 x1) (@CROSS a1 a0 (@UNIV a0) (@UNIV a1))).
Definition term73 (a0 : Type') (a1 : Type') := fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, @SETSPEC (prod a0 a1) y0 ((fun y3 : a0 => fun y4 : a1 => True) y1 y2) (@pair a0 a1 y1 y2).
Definition term56 (a0 : Type') (a1 : Type') := fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, @SETSPEC (prod a0 a1) y0 True (@pair a0 a1 y1 y2).
Definition term55 (a0 : Type') (a1 : Type') := fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, @SETSPEC (prod a0 a1) y0 ((@IN a0 y1 (@UNIV a0)) /\ (@IN a1 y2 (@UNIV a1))) (@pair a0 a1 y1 y2).
Definition term48 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : a0) := fun y0 : a1 => @SETSPEC (prod a0 a1) x0 True (@pair a0 a1 x1 y0).
Definition term13 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term28 (a0 : Type') (a1 : Type') := @eq Prop (forall y0 : prod a0 a1, (fun y1 : prod a0 a1 => (@IN (prod a0 a1) y1 (@CROSS a1 a0 (@UNIV a0) (@UNIV a1))) = (@IN (prod a0 a1) y1 (@UNIV (prod a0 a1)))) y0).
Definition term52 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := fun y0 : a0 => exists y1 : a1, @SETSPEC (prod a0 a1) x0 True (@pair a0 a1 y0 y1).
Definition term31 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @IN (prod a0 a1) (@pair a0 a1 x0 x1) (@CROSS a1 a0 (@UNIV a0) (@UNIV a1)).
Definition term44 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : a0) (x2 : a1) := @SETSPEC (prod a0 a1) x0 ((@IN a0 x1 (@UNIV a0)) /\ (@IN a1 x2 (@UNIV a1))).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) (x2 : type1470 a0 a1) := @IN (prod a1 a0) (@pair a1 a0 x0 x1) (@GSPEC (prod a1 a0) (fun y0 : prod a1 a0 => exists y1 : a1, exists y2 : a0, @SETSPEC (prod a1 a0) y0 (x2 y1 y2) (@pair a1 a0 y1 y2))).
Definition term16 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@CROSS a0 a1 x0 y0) = (@GSPEC (prod a1 a0) (fun y1 : prod a1 a0 => exists y2 : a1, exists y3 : a0, @SETSPEC (prod a1 a0) y1 ((@IN a1 y2 x0) /\ (@IN a0 y3 y0)) (@pair a1 a0 y2 y3)))) x1.
Definition term63 (a0 : Type') (a1 : Type') := fun y0 : a0 => fun y1 : a1 => True.
Definition term18 (a0 : Type') (a1 : Type') (x0 : type1210 a0 a1) (x1 : type1210 a0 a1) := forall y0 : prod a0 a1, (@IN (prod a0 a1) y0 x0) = (@IN (prod a0 a1) y0 x1).
Definition term36 (a0 : Type') (a1 : Type') (x0 : a0) := forall y0 : a1, (@IN (prod a0 a1) (@pair a0 a1 x0 y0) (@CROSS a1 a0 (@UNIV a0) (@UNIV a1))) = (@IN (prod a0 a1) (@pair a0 a1 x0 y0) (@UNIV (prod a0 a1))).
Definition term8 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) (x2 : a0) := (fun y0 : a0 => (@IN (prod a1 a0) (@pair a1 a0 x1 y0) (@GSPEC (prod a1 a0) (fun y1 : prod a1 a0 => exists y2 : a1, exists y3 : a0, @SETSPEC (prod a1 a0) y1 (x0 y2 y3) (@pair a1 a0 y2 y3)))) = (x0 x1 y0)) x2.
Definition term0 (a0 : Type') (x0 : a0) := (fun y0 : a0 => @IN a0 y0 (@UNIV a0)) x0.
Definition term6 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := (fun y0 : a1 => forall y1 : a0, (@IN (prod a1 a0) (@pair a1 a0 y0 y1) (@GSPEC (prod a1 a0) (fun y2 : prod a1 a0 => exists y3 : a1, exists y4 : a0, @SETSPEC (prod a1 a0) y2 (x0 y3 y4) (@pair a1 a0 y3 y4)))) = (x0 y0 y1)) x1.
Definition term49 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : a0) := exists y0 : a1, @SETSPEC (prod a0 a1) x0 ((@IN a0 x1 (@UNIV a0)) /\ (@IN a1 y0 (@UNIV a1))) (@pair a0 a1 x1 y0).
Definition term65 (a0 : Type') := fun y0 : a0 => True.
Definition term7 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) (x1 : a1) := forall y0 : a0, (@IN (prod a1 a0) (@pair a1 a0 x1 y0) (@GSPEC (prod a1 a0) (fun y1 : prod a1 a0 => exists y2 : a1, exists y3 : a0, @SETSPEC (prod a1 a0) y1 (x0 y2 y3) (@pair a1 a0 y2 y3)))) = (x0 x1 y0).
Definition term10 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (y0 = y1) = (forall y2 : a0, (@IN a0 y2 y0) = (@IN a0 y2 y1))) x0.
Definition term22 (a0 : Type') (a1 : Type') := forall y0 : prod a0 a1, (fun y1 : prod a0 a1 => (@IN (prod a0 a1) y1 (@CROSS a1 a0 (@UNIV a0) (@UNIV a1))) = (@IN (prod a0 a1) y1 (@UNIV (prod a0 a1)))) y0.
Definition term21 (a0 : Type') (a1 : Type') (x0 : type1210 a0 a1) := forall y0 : a0, forall y1 : a1, x0 (@pair a0 a1 y0 y1).
Definition term46 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : a0) (x2 : a1) := @SETSPEC (prod a0 a1) x0 True (@pair a0 a1 x1 x2).
Definition term62 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (fun y0 : a0 => fun y1 : a1 => True) x0 x1.
Definition term33 (a0 : Type') (a1 : Type') (x0 : a0) := fun y0 : a1 => (fun y1 : prod a0 a1 => (@IN (prod a0 a1) y1 (@CROSS a1 a0 (@UNIV a0) (@UNIV a1))) = (@IN (prod a0 a1) y1 (@UNIV (prod a0 a1)))) (@pair a0 a1 x0 y0).
Definition term24 (a0 : Type') (a1 : Type') := fun y0 : prod a0 a1 => (@IN (prod a0 a1) y0 (@CROSS a1 a0 (@UNIV a0) (@UNIV a1))) = (@IN (prod a0 a1) y0 (@UNIV (prod a0 a1))).
Definition term3 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : a1, forall y1 : a0, x0 (@pair a1 a0 y0 y1).
Definition term76 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @eq Prop (@IN (prod a0 a1) (@pair a0 a1 x0 x1) (@GSPEC (prod a0 a1) (fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, @SETSPEC (prod a0 a1) y0 True (@pair a0 a1 y1 y2)))).
Definition term75 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @eq Prop (@IN (prod a0 a1) (@pair a0 a1 x0 x1) (@GSPEC (prod a0 a1) (fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, @SETSPEC (prod a0 a1) y0 ((fun y3 : a0 => fun y4 : a1 => True) y1 y2) (@pair a0 a1 y1 y2)))).
Definition term19 (a0 : Type') (a1 : Type') := forall y0 : prod a0 a1, (@IN (prod a0 a1) y0 (@CROSS a1 a0 (@UNIV a0) (@UNIV a1))) = (@IN (prod a0 a1) y0 (@UNIV (prod a0 a1))).
Definition term34 (a0 : Type') (a1 : Type') (x0 : a0) := fun y0 : a1 => (@IN (prod a0 a1) (@pair a0 a1 x0 y0) (@CROSS a1 a0 (@UNIV a0) (@UNIV a1))) = (@IN (prod a0 a1) (@pair a0 a1 x0 y0) (@UNIV (prod a0 a1))).
Definition term15 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := forall y0 : a0 -> Prop, (@CROSS a0 a1 x0 y0) = (@GSPEC (prod a1 a0) (fun y1 : prod a1 a0 => exists y2 : a1, exists y3 : a0, @SETSPEC (prod a1 a0) y1 ((@IN a1 y2 x0) /\ (@IN a0 y3 y0)) (@pair a1 a0 y2 y3))).
Definition term50 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : a0) := exists y0 : a1, @SETSPEC (prod a0 a1) x0 True (@pair a0 a1 x1 y0).
Definition term69 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : a0) := fun y0 : a1 => @SETSPEC (prod a0 a1) x0 ((fun y1 : a0 => fun y2 : a1 => True) x1 y0) (@pair a0 a1 x1 y0).
Definition term30 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (fun y0 : prod a0 a1 => (@IN (prod a0 a1) y0 (@CROSS a1 a0 (@UNIV a0) (@UNIV a1))) = (@IN (prod a0 a1) y0 (@UNIV (prod a0 a1)))) (@pair a0 a1 x0 x1).
Definition term25 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := (fun y0 : prod a0 a1 => (@IN (prod a0 a1) y0 (@CROSS a1 a0 (@UNIV a0) (@UNIV a1))) = (@IN (prod a0 a1) y0 (@UNIV (prod a0 a1)))) x0.
Definition term74 (a0 : Type') (a1 : Type') := @GSPEC (prod a0 a1) (fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, @SETSPEC (prod a0 a1) y0 ((fun y3 : a0 => fun y4 : a1 => True) y1 y2) (@pair a0 a1 y1 y2)).
Definition term57 (a0 : Type') (a1 : Type') := @GSPEC (prod a0 a1) (fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, @SETSPEC (prod a0 a1) y0 True (@pair a0 a1 y1 y2)).
Definition term41 (a0 : Type') (a1 : Type') := @GSPEC (prod a0 a1) (fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, @SETSPEC (prod a0 a1) y0 ((@IN a0 y1 (@UNIV a0)) /\ (@IN a1 y2 (@UNIV a1))) (@pair a0 a1 y1 y2)).
Definition term40 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) := @GSPEC (prod a0 a1) (fun y0 : prod a0 a1 => exists y1 : a0, exists y2 : a1, @SETSPEC (prod a0 a1) y0 ((@IN a0 y1 x0) /\ (@IN a1 y2 x1)) (@pair a0 a1 y1 y2)).
Definition term17 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) := @GSPEC (prod a1 a0) (fun y0 : prod a1 a0 => exists y1 : a1, exists y2 : a0, @SETSPEC (prod a1 a0) y0 ((@IN a1 y1 x0) /\ (@IN a0 y2 x1)) (@pair a1 a0 y1 y2)).
Definition term29 (a0 : Type') (a1 : Type') := @eq Prop (forall y0 : prod a0 a1, (@IN (prod a0 a1) y0 (@CROSS a1 a0 (@UNIV a0) (@UNIV a1))) = (@IN (prod a0 a1) y0 (@UNIV (prod a0 a1)))).
Definition term39 (a0 : Type') (a1 : Type') := forall y0 : a0, forall y1 : a1, (@IN (prod a0 a1) (@pair a0 a1 y0 y1) (@CROSS a1 a0 (@UNIV a0) (@UNIV a1))) = (@IN (prod a0 a1) (@pair a0 a1 y0 y1) (@UNIV (prod a0 a1))).
Definition term5 (a0 : Type') (a1 : Type') (x0 : type1470 a0 a1) := forall y0 : a1, forall y1 : a0, (@IN (prod a1 a0) (@pair a1 a0 y0 y1) (@GSPEC (prod a1 a0) (fun y2 : prod a1 a0 => exists y3 : a1, exists y4 : a0, @SETSPEC (prod a1 a0) y2 (x0 y3 y4) (@pair a1 a0 y3 y4)))) = (x0 y0 y1).
Definition term32 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @IN (prod a0 a1) (@pair a0 a1 x0 x1) (@UNIV (prod a0 a1)).
Definition term68 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : a0) (x2 : a1) := @SETSPEC (prod a0 a1) x0 ((fun y0 : a0 => fun y1 : a1 => True) x1 x2) (@pair a0 a1 x1 x2).
Definition term58 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @IN (prod a0 a1) (@pair a0 a1 x0 x1).
Definition term45 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : a0) (x2 : a1) := @SETSPEC (prod a0 a1) x0 ((@IN a0 x1 (@UNIV a0)) /\ (@IN a1 x2 (@UNIV a1))) (@pair a0 a1 x1 x2).
Definition term42 (a0 : Type') (x0 : a0) := and (@IN a0 x0 (@UNIV a0)).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) := (fun y0 : a1 -> Prop => forall y1 : a0 -> Prop, (@CROSS a0 a1 y0 y1) = (@GSPEC (prod a1 a0) (fun y2 : prod a1 a0 => exists y3 : a1, exists y4 : a0, @SETSPEC (prod a1 a0) y2 ((@IN a1 y3 y0) /\ (@IN a0 y4 y1)) (@pair a1 a0 y3 y4)))) x0.
Definition term27 (a0 : Type') (a1 : Type') := fun y0 : prod a0 a1 => (fun y1 : prod a0 a1 => (@IN (prod a0 a1) y1 (@CROSS a1 a0 (@UNIV a0) (@UNIV a1))) = (@IN (prod a0 a1) y1 (@UNIV (prod a0 a1)))) y0.
Definition term70 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : a0) := exists y0 : a1, @SETSPEC (prod a0 a1) x0 ((fun y1 : a0 => fun y2 : a1 => True) x1 y0) (@pair a0 a1 x1 y0).
Definition term38 (a0 : Type') (a1 : Type') := fun y0 : a0 => forall y1 : a1, (@IN (prod a0 a1) (@pair a0 a1 y0 y1) (@CROSS a1 a0 (@UNIV a0) (@UNIV a1))) = (@IN (prod a0 a1) (@pair a0 a1 y0 y1) (@UNIV (prod a0 a1))).
Definition term12 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (x0 = y0) = (forall y1 : a0, (@IN a0 y1 x0) = (@IN a0 y1 y0))) x1.
Definition term37 (a0 : Type') (a1 : Type') := fun y0 : a0 => forall y1 : a1, (fun y2 : prod a0 a1 => (@IN (prod a0 a1) y2 (@CROSS a1 a0 (@UNIV a0) (@UNIV a1))) = (@IN (prod a0 a1) y2 (@UNIV (prod a0 a1)))) (@pair a0 a1 y0 y1).
Definition term66 (a0 : Type') (x0 : a0) := (fun y0 : a0 => True) x0.
Definition term71 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) := fun y0 : a0 => exists y1 : a1, @SETSPEC (prod a0 a1) x0 ((fun y2 : a0 => fun y3 : a1 => True) y0 y1) (@pair a0 a1 y0 y1).
Definition term43 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (@IN a0 x0 (@UNIV a0)) /\ (@IN a1 x1 (@UNIV a1)).
Definition term64 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => fun y1 : a1 => True) x0.
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (fun y0 : type1223 a0 a1 => (forall y1 : prod a1 a0, y0 y1) = (forall y1 : a1, forall y2 : a0, y0 (@pair a1 a0 y1 y2))) x0.
Definition term11 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (x0 = y0) = (forall y1 : a0, (@IN a0 y1 x0) = (@IN a0 y1 y0)).
Definition term67 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : a0) (x2 : a1) := @SETSPEC (prod a0 a1) x0 ((fun y0 : a0 => fun y1 : a1 => True) x1 x2).
