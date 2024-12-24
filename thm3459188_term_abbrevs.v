Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : type1470 a0 a1) := @IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => (fun y1 : type1527 a0 => exists y2 : a1, y1 (x1 y2) (x2 y2)) (@SETSPEC (a0 -> Prop) y0))).
Definition term22 (a0 : Type') (x0 : type1527 a0) (x1 : Prop) := (fun y0 : Prop => x0 y0) x1.
Definition term12 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) (x2 : a0 -> Prop) := (fun y0 : type1527 a0 => exists y1 : a1, y0 (x0 y1) (x1 y1)) (@SETSPEC (a0 -> Prop) x2).
Definition term1 (a0 : Type') (x0 : type686 a0) (x1 : a0) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 x0) -> @IN a0 x1 y0.
Definition term65 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1 -> Prop) (x2 : type1470 a0 a1) := exists y0 : a0, @SETSPEC a0 x0 ((fun y1 : a0 => forall y2 : a1, (x1 y2) -> @IN a0 y1 (x2 y2)) y0) y0.
Definition term34 (a0 : Type') (x0 : type686 a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => x0 y0) x1.
Definition term74 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) := fun y0 : a0 => (@IN a0 y0 (@INTERS a0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a1, @SETSPEC (a0 -> Prop) y1 (x0 y2) (x1 y2))))) = (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (forall y3 : a1, (x0 y3) -> @IN a0 y2 (x1 y3)) y2))).
Definition term48 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) (x2 : a0) (x3 : a0 -> Prop) := (exists y0 : a1, (x0 y0) /\ (x3 = (x1 y0))) -> @IN a0 x2 x3.
Definition term41 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : type1470 a0 a1) (x3 : a1) := (x0 x3) /\ (x1 = (x2 x3)).
Definition term49 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) (x2 : a0) := fun y0 : a0 -> Prop => (@IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a1, @SETSPEC (a0 -> Prop) y1 (x0 y2) (x1 y2)))) -> @IN a0 x2 y0.
Definition term11 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) := fun y0 : type1527 a0 => exists y1 : a1, y0 (x0 y1) (x1 y1).
Definition term30 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a1) := @eq ((a0 -> Prop) -> Prop) ((fun y0 : Prop => fun y1 : a0 -> Prop => y0 /\ (x0 = y1)) (x1 x2)).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : type1470 a0 a1) := exists y0 : a1, @SETSPEC (a0 -> Prop) x0 (x1 y0) (x2 y0).
Definition term10 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) (x2 : a0 -> Prop) := (fun y0 : type1527 a0 => exists y1 : a1, y0 (x0 y1) (x1 y1)) (fun y0 : Prop => fun y1 : a0 -> Prop => y0 /\ (x2 = y1)).
Definition term15 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) := fun y0 : a0 -> Prop => exists y1 : a1, @SETSPEC (a0 -> Prop) y0 (x0 y1) (x1 y1).
Definition term68 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (forall y2 : a1, (x0 y2) -> @IN a0 y1 (x1 y2)) y1.
Definition term52 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1 -> Prop) (x2 : type1470 a0 a1) := @eq Prop (@IN a0 x0 (@INTERS a0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a1, @SETSPEC (a0 -> Prop) y0 (x1 y1) (x2 y1))))).
Definition term67 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) := fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => forall y3 : a1, (x0 y3) -> @IN a0 y2 (x1 y3)) y1) y1.
Definition term38 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1) (x2 : a0 -> Prop) := fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => (x0 x1) /\ (x2 = y1)) y0.
Definition term59 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1 -> Prop) (x2 : type1470 a0 a1) (x3 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => forall y1 : a1, (x1 y1) -> @IN a0 y0 (x2 y1)) x3).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : Prop => fun y1 : a0 -> Prop => y0 /\ (x0 = y1).
Definition term35 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : type1470 a0 a1) (x3 : a1) := (fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => (x0 x3) /\ (x1 = y1)) y0) (x2 x3).
Definition term23 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a1) := (fun y0 : Prop => (fun y1 : Prop => fun y2 : a0 -> Prop => y1 /\ (x0 = y2)) y0) (x1 x2).
Definition term77 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) := forall y0 : a0, (forall y1 : a0 -> Prop, (exists y2 : a1, (x0 y2) /\ (y1 = (x1 y2))) -> @IN a0 y0 y1) = (forall y1 : a1, (x0 y1) -> @IN a0 y0 (x1 y1)).
Definition term71 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1 -> Prop) (x2 : type1470 a0 a1) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (forall y2 : a1, (x1 y2) -> @IN a0 y1 (x2 y2)) y1)).
Definition term55 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1 -> Prop) (x2 : type1470 a0 a1) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => forall y3 : a1, (x1 y3) -> @IN a0 y2 (x2 y3)) y1) y1)).
Definition term54 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (x1 y1) y1)).
Definition term61 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1 -> Prop) (x2 : type1470 a0 a1) (x3 : a0) := @SETSPEC a0 x0 ((fun y0 : a0 => forall y1 : a1, (x1 y1) -> @IN a0 y0 (x2 y1)) x3) x3.
Definition term32 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : type1470 a0 a1) (x3 : a1) := (fun y0 : Prop => fun y1 : a0 -> Prop => y0 /\ (x0 = y1)) (x1 x3) (x2 x3).
Definition term45 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : type1470 a0 a1) := imp (@IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a1, @SETSPEC (a0 -> Prop) y0 (x1 y1) (x2 y1)))).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : type909 a0) := @IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => x1 (@SETSPEC (a0 -> Prop) y0))).
Definition term66 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1 -> Prop) (x2 : type1470 a0 a1) := exists y0 : a0, @SETSPEC a0 x0 (forall y1 : a1, (x1 y1) -> @IN a0 y0 (x2 y1)) y0.
Definition term73 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1 -> Prop) (x2 : type1470 a0 a1) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (forall y2 : a1, (x1 y2) -> @IN a0 y1 (x2 y2)) y1))).
Definition term72 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1 -> Prop) (x2 : type1470 a0 a1) := @eq Prop (@IN a0 x0 (@GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => forall y3 : a1, (x1 y3) -> @IN a0 y2 (x2 y3)) y1) y1))).
Definition term21 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term70 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 (forall y2 : a1, (x0 y2) -> @IN a0 y1 (x1 y2)) y1).
Definition term69 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) := @GSPEC a0 (fun y0 : a0 => exists y1 : a0, @SETSPEC a0 y0 ((fun y2 : a0 => forall y3 : a1, (x0 y3) -> @IN a0 y2 (x1 y3)) y1) y1).
Definition term58 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0) (x2 : type1470 a0 a1) := forall y0 : a1, (x0 y0) -> @IN a0 x1 (x2 y0).
Definition term33 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : type1470 a0 a1) (x3 : a1) := (fun y0 : a0 -> Prop => (x0 x3) /\ (x1 = y0)) (x2 x3).
Definition term20 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : type1470 a0 a1) := exists y0 : a1, (fun y1 : Prop => fun y2 : a0 -> Prop => y1 /\ (x0 = y2)) (x1 y0) (x2 y0).
Definition term63 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1 -> Prop) (x2 : type1470 a0 a1) := fun y0 : a0 => @SETSPEC a0 x0 ((fun y1 : a0 => forall y2 : a1, (x1 y2) -> @IN a0 y1 (x2 y2)) y0) y0.
Definition term14 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) := fun y0 : a0 -> Prop => (fun y1 : type1527 a0 => exists y2 : a1, y1 (x0 y2) (x1 y2)) (@SETSPEC (a0 -> Prop) y0).
Definition term53 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) (x2 : a0) := @eq Prop (forall y0 : a0 -> Prop, (exists y1 : a1, (x0 y1) /\ (y0 = (x1 y1))) -> @IN a0 x2 y0).
Definition term24 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a1) := (fun y0 : Prop => fun y1 : a0 -> Prop => y0 /\ (x0 = y1)) (x1 x2).
Definition term75 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) := fun y0 : a0 => (forall y1 : a0 -> Prop, (exists y2 : a1, (x0 y2) /\ (y1 = (x1 y2))) -> @IN a0 y0 y1) = (forall y1 : a1, (x0 y1) -> @IN a0 y0 (x1 y1)).
Definition term0 (a0 : Type') (x0 : a0) (x1 : type686 a0) := @IN a0 x0 (@INTERS a0 x1).
Definition term28 (a0 : Type') (x0 : a0 -> Prop) := fun y0 : Prop => (fun y1 : Prop => fun y2 : a0 -> Prop => y1 /\ (x0 = y2)) y0.
Definition term29 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : a1) := @eq ((a0 -> Prop) -> Prop) ((fun y0 : Prop => (fun y1 : Prop => fun y2 : a0 -> Prop => y1 /\ (x0 = y2)) y0) (x1 x2)).
Definition term62 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1 -> Prop) (x2 : type1470 a0 a1) (x3 : a0) := @SETSPEC a0 x0 (forall y0 : a1, (x1 y0) -> @IN a0 x3 (x2 y0)) x3.
Definition term16 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) := @GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => (fun y1 : type1527 a0 => exists y2 : a1, y1 (x0 y2) (x1 y2)) (@SETSPEC (a0 -> Prop) y0)).
Definition term19 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : type1470 a0 a1) := @eq Prop (@IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a1, @SETSPEC (a0 -> Prop) y0 (x1 y1) (x2 y1)))).
Definition term18 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : type1470 a0 a1) := @eq Prop (@IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => (fun y1 : type1527 a0 => exists y2 : a1, y1 (x1 y2) (x2 y2)) (@SETSPEC (a0 -> Prop) y0)))).
Definition term40 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : type1470 a0 a1) (x3 : a1) := @eq Prop ((fun y0 : a0 -> Prop => (x0 x3) /\ (x1 = y0)) (x2 x3)).
Definition term36 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := (fun y0 : a0 -> Prop => (x0 x1) /\ (x2 = y0)) x3.
Definition term5 (a0 : Type') (x0 : a0) (x1 : type919 a0) := @IN a0 x0 (@GSPEC a0 (fun y0 : a0 => x1 (@SETSPEC a0 y0))).
Definition term60 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1 -> Prop) (x2 : a0) (x3 : type1470 a0 a1) := @SETSPEC a0 x0 (forall y0 : a1, (x1 y0) -> @IN a0 x2 (x3 y0)).
Definition term43 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : type1470 a0 a1) := fun y0 : a1 => (x0 y0) /\ (x1 = (x2 y0)).
Definition term44 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : type1470 a0 a1) := exists y0 : a1, (x0 y0) /\ (x1 = (x2 y0)).
Definition term6 (a0 : Type') (x0 : type919 a0) (x1 : a0) := x0 (fun y0 : Prop => fun y1 : a0 => y0 /\ (x1 = y1)).
Definition term50 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) (x2 : a0) := fun y0 : a0 -> Prop => (exists y1 : a1, (x0 y1) /\ (y0 = (x1 y1))) -> @IN a0 x2 y0.
Definition term47 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) (x2 : a0) (x3 : a0 -> Prop) := (@IN (a0 -> Prop) x3 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a1, @SETSPEC (a0 -> Prop) y0 (x0 y1) (x1 y1)))) -> @IN a0 x2 x3.
Definition term42 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : type1470 a0 a1) := fun y0 : a1 => (fun y1 : Prop => fun y2 : a0 -> Prop => y1 /\ (x0 = y2)) (x1 y0) (x2 y0).
Definition term17 (a0 : Type') (a1 : Type') (x0 : a0 -> Prop) (x1 : a1 -> Prop) (x2 : type1470 a0 a1) := @IN (a0 -> Prop) x0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a1, @SETSPEC (a0 -> Prop) y0 (x1 y1) (x2 y1))).
Definition term37 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1) (x2 : a0 -> Prop) (x3 : a0 -> Prop) := (x0 x1) /\ (x2 = x3).
Definition term46 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : type1470 a0 a1) := imp (exists y0 : a1, (x0 y0) /\ (x1 = (x2 y0))).
Definition term39 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a0 -> Prop) (x2 : type1470 a0 a1) (x3 : a1) := @eq Prop ((fun y0 : a0 -> Prop => (fun y1 : a0 -> Prop => (x0 x3) /\ (x1 = y1)) y0) (x2 x3)).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1 -> Prop) (x2 : type1470 a0 a1) := @IN a0 x0 (@INTERS a0 (@GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a1, @SETSPEC (a0 -> Prop) y0 (x1 y1) (x2 y1)))).
Definition term8 (a0 : Type') (x0 : type909 a0) (x1 : a0 -> Prop) := x0 (fun y0 : Prop => fun y1 : a0 -> Prop => y0 /\ (x1 = y1)).
Definition term27 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := fun y0 : a0 -> Prop => x0 /\ (x1 = y0).
Definition term56 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) (x2 : a0) := (fun y0 : a0 => forall y1 : a1, (x0 y1) -> @IN a0 y0 (x1 y1)) x2.
Definition term76 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) := forall y0 : a0, (@IN a0 y0 (@INTERS a0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a1, @SETSPEC (a0 -> Prop) y1 (x0 y2) (x1 y2))))) = (@IN a0 y0 (@GSPEC a0 (fun y1 : a0 => exists y2 : a0, @SETSPEC a0 y1 (forall y3 : a1, (x0 y3) -> @IN a0 y2 (x1 y3)) y2))).
Definition term64 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1 -> Prop) (x2 : type1470 a0 a1) := fun y0 : a0 => @SETSPEC a0 x0 (forall y1 : a1, (x1 y1) -> @IN a0 y0 (x2 y1)) y0.
Definition term26 (a0 : Type') (x0 : a0 -> Prop) (x1 : Prop) := (fun y0 : Prop => fun y1 : a0 -> Prop => y0 /\ (x0 = y1)) x1.
Definition term31 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : a1) (x2 : a0 -> Prop) := fun y0 : a0 -> Prop => (x0 x1) /\ (x2 = y0).
Definition term51 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) (x2 : a0) := forall y0 : a0 -> Prop, (exists y1 : a1, (x0 y1) /\ (y0 = (x1 y1))) -> @IN a0 x2 y0.
Definition term3 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) (x2 : a0) := forall y0 : a0 -> Prop, (@IN (a0 -> Prop) y0 (@GSPEC (a0 -> Prop) (fun y1 : a0 -> Prop => exists y2 : a1, @SETSPEC (a0 -> Prop) y1 (x0 y2) (x1 y2)))) -> @IN a0 x2 y0.
Definition term4 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) := @GSPEC (a0 -> Prop) (fun y0 : a0 -> Prop => exists y1 : a1, @SETSPEC (a0 -> Prop) y0 (x0 y1) (x1 y1)).
Definition term57 (a0 : Type') (a1 : Type') (x0 : a1 -> Prop) (x1 : type1470 a0 a1) := fun y0 : a0 => forall y1 : a1, (x0 y1) -> @IN a0 y0 (x1 y1).
