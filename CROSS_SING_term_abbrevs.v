Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term39 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : a0) (x2 : a1) := @IN (prod a0 a1) x0 (@INSERT (prod a0 a1) (@pair a0 a1 x1 x2) (@EMPTY (prod a0 a1))).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a1) := forall y0 : a1 -> Prop, (@IN (prod a0 a1) (@pair a0 a1 x0 x2) (@CROSS a1 a0 x1 y0)) = ((@IN a0 x0 x1) /\ (@IN a1 x2 y0)).
Definition term51 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := fun y0 : a0 => forall y1 : a1, (@IN (prod a0 a1) (@pair a0 a1 y0 y1) (@CROSS a1 a0 (@INSERT a0 x0 (@EMPTY a0)) (@INSERT a1 x1 (@EMPTY a1)))) = (@IN (prod a0 a1) (@pair a0 a1 y0 y1) (@INSERT (prod a0 a1) (@pair a0 a1 x0 x1) (@EMPTY (prod a0 a1)))).
Definition term45 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a0) (x3 : a1) := @IN (prod a0 a1) (@pair a0 a1 x0 x1) (@INSERT (prod a0 a1) (@pair a0 a1 x2 x3) (@EMPTY (prod a0 a1))).
Definition term48 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a0) := forall y0 : a1, (fun y1 : prod a0 a1 => (@IN (prod a0 a1) y1 (@CROSS a1 a0 (@INSERT a0 x0 (@EMPTY a0)) (@INSERT a1 x1 (@EMPTY a1)))) = (@IN (prod a0 a1) y1 (@INSERT (prod a0 a1) (@pair a0 a1 x0 x1) (@EMPTY (prod a0 a1))))) (@pair a0 a1 x2 y0).
Definition term38 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : a0) (x2 : a1) := @IN (prod a0 a1) x0 (@CROSS a1 a0 (@INSERT a0 x1 (@EMPTY a0)) (@INSERT a1 x2 (@EMPTY a1))).
Definition term35 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := forall y0 : a0, forall y1 : a1, (fun y2 : prod a0 a1 => (@IN (prod a0 a1) y2 (@CROSS a1 a0 (@INSERT a0 x0 (@EMPTY a0)) (@INSERT a1 x1 (@EMPTY a1)))) = (@IN (prod a0 a1) y2 (@INSERT (prod a0 a1) (@pair a0 a1 x0 x1) (@EMPTY (prod a0 a1))))) (@pair a0 a1 y0 y1).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (fun y0 : a1 => forall y1 : a0, forall y2 : a1, ((@pair a0 a1 x0 y0) = (@pair a0 a1 y1 y2)) = ((x0 = y1) /\ (y0 = y2))) x1.
Definition term32 (a0 : Type') (a1 : Type') (x0 : type1210 a0 a1) := forall y0 : prod a0 a1, x0 y0.
Definition term22 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : prod a1 a0, x0 y0.
Definition term46 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a0) := fun y0 : a1 => (fun y1 : prod a0 a1 => (@IN (prod a0 a1) y1 (@CROSS a1 a0 (@INSERT a0 x0 (@EMPTY a0)) (@INSERT a1 x1 (@EMPTY a1)))) = (@IN (prod a0 a1) y1 (@INSERT (prod a0 a1) (@pair a0 a1 x0 x1) (@EMPTY (prod a0 a1))))) (@pair a0 a1 x2 y0).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a1, forall y2 : a0 -> Prop, forall y3 : a1 -> Prop, (@IN (prod a0 a1) (@pair a0 a1 y0 y1) (@CROSS a1 a0 y2 y3)) = ((@IN a0 y0 y2) /\ (@IN a1 y1 y3))) x0.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a1, forall y2 : a0, forall y3 : a1, ((@pair a0 a1 y0 y1) = (@pair a0 a1 y2 y3)) = ((y0 = y2) /\ (y1 = y3))) x0.
Definition term61 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term47 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0) (x2 : a1) := fun y0 : a1 => (@IN (prod a0 a1) (@pair a0 a1 x0 y0) (@CROSS a1 a0 (@INSERT a0 x1 (@EMPTY a0)) (@INSERT a1 x2 (@EMPTY a1)))) = (@IN (prod a0 a1) (@pair a0 a1 x0 y0) (@INSERT (prod a0 a1) (@pair a0 a1 x1 x2) (@EMPTY (prod a0 a1)))).
Definition term19 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => (@IN a0 x0 (@INSERT a0 y0 (@EMPTY a0))) = (x0 = y0)) x1.
Definition term60 (a0 : Type') := forall y0 : a0, True.
Definition term16 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a1) (x3 : a1 -> Prop) := (@IN a0 x0 x1) /\ (@IN a1 x2 x3).
Definition term40 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := fun y0 : prod a0 a1 => (fun y1 : prod a0 a1 => (@IN (prod a0 a1) y1 (@CROSS a1 a0 (@INSERT a0 x0 (@EMPTY a0)) (@INSERT a1 x1 (@EMPTY a1)))) = (@IN (prod a0 a1) y1 (@INSERT (prod a0 a1) (@pair a0 a1 x0 x1) (@EMPTY (prod a0 a1))))) y0.
Definition term58 (a0 : Type') (a1 : Type') (x0 : prod a0 a1) (x1 : prod a0 a1) := @IN (prod a0 a1) x0 (@INSERT (prod a0 a1) x1 (@EMPTY (prod a0 a1))).
Definition term27 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (@IN a0 y0 x0) = (@IN a0 y0 x1).
Definition term53 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0) (x2 : a1) (x3 : a1) := (@IN a0 x0 (@INSERT a0 x1 (@EMPTY a0))) /\ (@IN a1 x2 (@INSERT a1 x3 (@EMPTY a1))).
Definition term62 (a0 : Type') (a1 : Type') (x0 : a0) := fun y0 : a1 => (@CROSS a1 a0 (@INSERT a0 x0 (@EMPTY a0)) (@INSERT a1 y0 (@EMPTY a1))) = (@INSERT (prod a0 a1) (@pair a0 a1 x0 y0) (@EMPTY (prod a0 a1))).
Definition term41 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @eq Prop (forall y0 : prod a0 a1, (fun y1 : prod a0 a1 => (@IN (prod a0 a1) y1 (@CROSS a1 a0 (@INSERT a0 x0 (@EMPTY a0)) (@INSERT a1 x1 (@EMPTY a1)))) = (@IN (prod a0 a1) y1 (@INSERT (prod a0 a1) (@pair a0 a1 x0 x1) (@EMPTY (prod a0 a1))))) y0).
Definition term44 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a0) (x3 : a1) := @IN (prod a0 a1) (@pair a0 a1 x0 x1) (@CROSS a1 a0 (@INSERT a0 x2 (@EMPTY a0)) (@INSERT a1 x3 (@EMPTY a1))).
Definition term17 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, (@IN a0 y0 (@INSERT a0 y1 (@EMPTY a0))) = (y0 = y1)) x0.
Definition term49 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0) (x2 : a1) := forall y0 : a1, (@IN (prod a0 a1) (@pair a0 a1 x0 y0) (@CROSS a1 a0 (@INSERT a0 x1 (@EMPTY a0)) (@INSERT a1 x2 (@EMPTY a1)))) = (@IN (prod a0 a1) (@pair a0 a1 x0 y0) (@INSERT (prod a0 a1) (@pair a0 a1 x1 x2) (@EMPTY (prod a0 a1)))).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0) (x2 : a1) (x3 : a1) := (fun y0 : a1 => ((@pair a0 a1 x0 x2) = (@pair a0 a1 x1 y0)) = ((x0 = x1) /\ (x2 = y0))) x3.
Definition term43 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a0) (x3 : a1) := (fun y0 : prod a0 a1 => (@IN (prod a0 a1) y0 (@CROSS a1 a0 (@INSERT a0 x0 (@EMPTY a0)) (@INSERT a1 x1 (@EMPTY a1)))) = (@IN (prod a0 a1) y0 (@INSERT (prod a0 a1) (@pair a0 a1 x0 x1) (@EMPTY (prod a0 a1))))) (@pair a0 a1 x2 x3).
Definition term36 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := fun y0 : prod a0 a1 => (@IN (prod a0 a1) y0 (@CROSS a1 a0 (@INSERT a0 x0 (@EMPTY a0)) (@INSERT a1 x1 (@EMPTY a1)))) = (@IN (prod a0 a1) y0 (@INSERT (prod a0 a1) (@pair a0 a1 x0 x1) (@EMPTY (prod a0 a1)))).
Definition term31 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := forall y0 : prod a0 a1, (@IN (prod a0 a1) y0 (@CROSS a1 a0 (@INSERT a0 x0 (@EMPTY a0)) (@INSERT a1 x1 (@EMPTY a1)))) = (@IN (prod a0 a1) y0 (@INSERT (prod a0 a1) (@pair a0 a1 x0 x1) (@EMPTY (prod a0 a1)))).
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a1 -> Prop, (@IN (prod a0 a1) (@pair a0 a1 x0 x1) (@CROSS a1 a0 y0 y1)) = ((@IN a0 x0 y0) /\ (@IN a1 x1 y1))) x2.
Definition term28 (a0 : Type') (a1 : Type') (x0 : type1210 a0 a1) (x1 : type1210 a0 a1) := forall y0 : prod a0 a1, (@IN (prod a0 a1) y0 x0) = (@IN (prod a0 a1) y0 x1).
Definition term54 (a0 : Type') (x0 : a0) (x1 : a0) := and (@IN a0 x0 (@INSERT a0 x1 (@EMPTY a0))).
Definition term59 (a0 : Type') := fun y0 : a0 => True.
Definition term29 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @CROSS a1 a0 (@INSERT a0 x0 (@EMPTY a0)) (@INSERT a1 x1 (@EMPTY a1)).
Definition term42 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @eq Prop (forall y0 : prod a0 a1, (@IN (prod a0 a1) y0 (@CROSS a1 a0 (@INSERT a0 x0 (@EMPTY a0)) (@INSERT a1 x1 (@EMPTY a1)))) = (@IN (prod a0 a1) y0 (@INSERT (prod a0 a1) (@pair a0 a1 x0 x1) (@EMPTY (prod a0 a1))))).
Definition term56 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a0) (x3 : a1) := @eq Prop (@IN (prod a0 a1) (@pair a0 a1 x0 x1) (@CROSS a1 a0 (@INSERT a0 x2 (@EMPTY a0)) (@INSERT a1 x3 (@EMPTY a1)))).
Definition term24 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (y0 = y1) = (forall y2 : a0, (@IN a0 y2 y0) = (@IN a0 y2 y1))) x0.
Definition term34 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := forall y0 : prod a0 a1, (fun y1 : prod a0 a1 => (@IN (prod a0 a1) y1 (@CROSS a1 a0 (@INSERT a0 x0 (@EMPTY a0)) (@INSERT a1 x1 (@EMPTY a1)))) = (@IN (prod a0 a1) y1 (@INSERT (prod a0 a1) (@pair a0 a1 x0 x1) (@EMPTY (prod a0 a1))))) y0.
Definition term33 (a0 : Type') (a1 : Type') (x0 : type1210 a0 a1) := forall y0 : a0, forall y1 : a1, x0 (@pair a0 a1 y0 y1).
Definition term15 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a0 -> Prop) (x3 : a1 -> Prop) := @IN (prod a0 a1) (@pair a0 a1 x0 x1) (@CROSS a1 a0 x2 x3).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a1) (x3 : a1 -> Prop) := (fun y0 : a1 -> Prop => (@IN (prod a0 a1) (@pair a0 a1 x0 x2) (@CROSS a1 a0 x1 y0)) = ((@IN a0 x0 x1) /\ (@IN a1 x2 y0))) x3.
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0) (x2 : a1) (x3 : a1) := (x0 = x1) /\ (x2 = x3).
Definition term55 (a0 : Type') (x0 : a0) (x1 : a0) := and (x0 = x1).
Definition term57 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0) (x2 : a1) (x3 : a1) := @eq Prop ((x0 = x1) /\ (x2 = x3)).
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := forall y0 : a0 -> Prop, forall y1 : a1 -> Prop, (@IN (prod a0 a1) (@pair a0 a1 x0 x1) (@CROSS a1 a0 y0 y1)) = ((@IN a0 x0 y0) /\ (@IN a1 x1 y1)).
Definition term23 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := forall y0 : a1, forall y1 : a0, x0 (@pair a1 a0 y0 y1).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0) := forall y0 : a1, forall y1 : a0 -> Prop, forall y2 : a1 -> Prop, (@IN (prod a0 a1) (@pair a0 a1 x0 y0) (@CROSS a1 a0 y1 y2)) = ((@IN a0 x0 y1) /\ (@IN a1 y0 y2)).
Definition term37 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : prod a0 a1) := (fun y0 : prod a0 a1 => (@IN (prod a0 a1) y0 (@CROSS a1 a0 (@INSERT a0 x0 (@EMPTY a0)) (@INSERT a1 x1 (@EMPTY a1)))) = (@IN (prod a0 a1) y0 (@INSERT (prod a0 a1) (@pair a0 a1 x0 x1) (@EMPTY (prod a0 a1))))) x2.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0) := forall y0 : a1, forall y1 : a0, forall y2 : a1, ((@pair a0 a1 x0 y0) = (@pair a0 a1 y1 y2)) = ((x0 = y1) /\ (y0 = y2)).
Definition term20 (a0 : Type') (x0 : a0) (x1 : a0) := @IN a0 x0 (@INSERT a0 x1 (@EMPTY a0)).
Definition term65 (a0 : Type') (a1 : Type') := forall y0 : a0, forall y1 : a1, (@CROSS a1 a0 (@INSERT a0 y0 (@EMPTY a0)) (@INSERT a1 y1 (@EMPTY a1))) = (@INSERT (prod a0 a1) (@pair a0 a1 y0 y1) (@EMPTY (prod a0 a1))).
Definition term52 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := forall y0 : a0, forall y1 : a1, (@IN (prod a0 a1) (@pair a0 a1 y0 y1) (@CROSS a1 a0 (@INSERT a0 x0 (@EMPTY a0)) (@INSERT a1 x1 (@EMPTY a1)))) = (@IN (prod a0 a1) (@pair a0 a1 y0 y1) (@INSERT (prod a0 a1) (@pair a0 a1 x0 x1) (@EMPTY (prod a0 a1)))).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := forall y0 : a0, forall y1 : a1, ((@pair a0 a1 x0 x1) = (@pair a0 a1 y0 y1)) = ((x0 = y0) /\ (x1 = y1)).
Definition term18 (a0 : Type') (x0 : a0) := forall y0 : a0, (@IN a0 x0 (@INSERT a0 y0 (@EMPTY a0))) = (x0 = y0).
Definition term5 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a0) (x2 : a1) := forall y0 : a1, ((@pair a0 a1 x0 x2) = (@pair a0 a1 x1 y0)) = ((x0 = x1) /\ (x2 = y0)).
Definition term4 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) (x2 : a0) := (fun y0 : a0 => forall y1 : a1, ((@pair a0 a1 x0 x1) = (@pair a0 a1 y0 y1)) = ((x0 = y0) /\ (x1 = y1))) x2.
Definition term26 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (x0 = y0) = (forall y1 : a0, (@IN a0 y1 x0) = (@IN a0 y1 y0))) x1.
Definition term50 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := fun y0 : a0 => forall y1 : a1, (fun y2 : prod a0 a1 => (@IN (prod a0 a1) y2 (@CROSS a1 a0 (@INSERT a0 x0 (@EMPTY a0)) (@INSERT a1 x1 (@EMPTY a1)))) = (@IN (prod a0 a1) y2 (@INSERT (prod a0 a1) (@pair a0 a1 x0 x1) (@EMPTY (prod a0 a1))))) (@pair a0 a1 y0 y1).
Definition term63 (a0 : Type') (a1 : Type') (x0 : a0) := forall y0 : a1, (@CROSS a1 a0 (@INSERT a0 x0 (@EMPTY a0)) (@INSERT a1 y0 (@EMPTY a1))) = (@INSERT (prod a0 a1) (@pair a0 a1 x0 y0) (@EMPTY (prod a0 a1))).
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (fun y0 : a1 => forall y1 : a0 -> Prop, forall y2 : a1 -> Prop, (@IN (prod a0 a1) (@pair a0 a1 x0 y0) (@CROSS a1 a0 y1 y2)) = ((@IN a0 x0 y1) /\ (@IN a1 y0 y2))) x1.
Definition term21 (a0 : Type') (a1 : Type') (x0 : type1223 a0 a1) := (fun y0 : type1223 a0 a1 => (forall y1 : prod a1 a0, y0 y1) = (forall y1 : a1, forall y2 : a0, y0 (@pair a1 a0 y1 y2))) x0.
Definition term64 (a0 : Type') (a1 : Type') := fun y0 : a0 => forall y1 : a1, (@CROSS a1 a0 (@INSERT a0 y0 (@EMPTY a0)) (@INSERT a1 y1 (@EMPTY a1))) = (@INSERT (prod a0 a1) (@pair a0 a1 y0 y1) (@EMPTY (prod a0 a1))).
Definition term25 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (x0 = y0) = (forall y1 : a0, (@IN a0 y1 x0) = (@IN a0 y1 y0)).
Definition term30 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @INSERT (prod a0 a1) (@pair a0 a1 x0 x1) (@EMPTY (prod a0 a1)).
