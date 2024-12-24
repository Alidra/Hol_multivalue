Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term58 (a0 : Type') := fun y0 : type1290 a0 => forall y1 : type1673, ((y0 y1 (@nil a0)) = True) /\ (forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = False).
Definition term49 (a0 : Type') := @eq Prop (forall y0 : type1673, exists y1 : type1143 a0, ((y1 (@nil a0)) = True) /\ (forall y2 : a0, forall y3 : list a0, (y1 (@cons a0 y2 y3)) = False)).
Definition term48 (a0 : Type') := @eq Prop (forall y0 : type1673, exists y1 : type1143 a0, (fun y2 : type1673 => fun y3 : type1143 a0 => ((y3 (@nil a0)) = True) /\ (forall y4 : a0, forall y5 : list a0, (y3 (@cons a0 y4 y5)) = False)) y0 y1).
Definition term28 (a0 : Type') (x0 : type1143 a0) := ((x0 (@nil a0)) = True) /\ (forall y0 : a0, forall y1 : list a0, (x0 (@cons a0 y0 y1)) = ((fun y2 : a0 => fun y3 : list a0 => fun y4 : Prop => False) y0 y1 (x0 y1))).
Definition term5 (a0 : Type') (x0 : type1143 a0) := ((x0 (@nil a0)) = True) /\ (forall y0 : a0, forall y1 : list a0, (x0 (@cons a0 y0 y1)) = False).
Definition term57 (a0 : Type') := fun y0 : type1290 a0 => forall y1 : type1673, (fun y2 : type1673 => fun y3 : type1143 a0 => ((y3 (@nil a0)) = True) /\ (forall y4 : a0, forall y5 : list a0, (y3 (@cons a0 y4 y5)) = False)) y1 (y0 y1).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a1) := (fun y0 : a1 => forall y1 : type1394 a0 a1, exists y2 : type1142 a0 a1, ((y2 (@nil a0)) = y0) /\ (forall y3 : a0, forall y4 : list a0, (y2 (@cons a0 y3 y4)) = (y1 y3 y4 (y2 y4)))) x0.
Definition term30 (a0 : Type') := fun y0 : type1143 a0 => ((y0 (@nil a0)) = True) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = False).
Definition term29 (a0 : Type') := fun y0 : type1143 a0 => ((y0 (@nil a0)) = True) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = ((fun y3 : a0 => fun y4 : list a0 => fun y5 : Prop => False) y1 y2 (y0 y2))).
Definition term24 (a0 : Type') (x0 : type1143 a0) := fun y0 : a0 => forall y1 : list a0, (x0 (@cons a0 y0 y1)) = ((fun y2 : a0 => fun y3 : list a0 => fun y4 : Prop => False) y0 y1 (x0 y1)).
Definition term13 (a0 : Type') (x0 : a0) := (fun y0 : a0 => fun y1 : list a0 => fun y2 : Prop => False) x0.
Definition term8 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1394 a0 a1) := (fun y0 : type1394 a0 a1 => exists y1 : type1142 a0 a1, ((y1 (@nil a0)) = x0) /\ (forall y2 : a0, forall y3 : list a0, (y1 (@cons a0 y2 y3)) = (y0 y2 y3 (y1 y3)))) x1.
Definition term52 (a0 : Type') (x0 : type1290 a0) (x1 : type1673) := ((x0 x1 (@nil a0)) = True) /\ (forall y0 : a0, forall y1 : list a0, (x0 x1 (@cons a0 y0 y1)) = False).
Definition term63 (a0 : Type') := (fun y0 : type1290 a0 => forall y1 : type1673, ((y0 y1 (@nil a0)) = True) /\ (forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = False)) (@ε ((prod nat (prod nat (prod nat nat))) -> (list a0) -> Prop) (fun y0 : type1290 a0 => forall y1 : type1673, ((y0 y1 (@nil a0)) = True) /\ (forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = False))).
Definition term2 (a0 : Type') (x0 : type1143 a0) (x1 : a0) := forall y0 : list a0, (x0 (@cons a0 x1 y0)) = False.
Definition term4 (a0 : Type') (x0 : type1143 a0) (x1 : a0) (x2 : list a0) := x0 (@cons a0 x1 x2).
Definition term34 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term59 (a0 : Type') := exists y0 : type1290 a0, forall y1 : type1673, ((y0 y1 (@nil a0)) = True) /\ (forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = False).
Definition term39 (a0 : Type') := exists y0 : type1290 a0, forall y1 : type1673, (fun y2 : type1673 => fun y3 : type1143 a0 => ((y3 (@nil a0)) = True) /\ (forall y4 : a0, forall y5 : list a0, (y3 (@cons a0 y4 y5)) = False)) y1 (y0 y1).
Definition term37 (a0 : Type') (x0 : type1284 a0) := exists y0 : type1290 a0, forall y1 : type1673, x0 y1 (y0 y1).
Definition term55 (a0 : Type') (x0 : type1290 a0) := forall y0 : type1673, (fun y1 : type1673 => fun y2 : type1143 a0 => ((y2 (@nil a0)) = True) /\ (forall y3 : a0, forall y4 : list a0, (y2 (@cons a0 y3 y4)) = False)) y0 (x0 y0).
Definition term25 (a0 : Type') (x0 : type1143 a0) := fun y0 : a0 => forall y1 : list a0, (x0 (@cons a0 y0 y1)) = False.
Definition term56 (a0 : Type') (x0 : type1290 a0) := forall y0 : type1673, ((x0 y0 (@nil a0)) = True) /\ (forall y1 : a0, forall y2 : list a0, (x0 y0 (@cons a0 y1 y2)) = False).
Definition term61 (a0 : Type') := fun y0 : type361 a0 => y0 (@ε ((prod nat (prod nat (prod nat nat))) -> (list a0) -> Prop) y0).
Definition term3 (a0 : Type') (x0 : type1143 a0) (x1 : a0) (x2 : list a0) := (fun y0 : list a0 => (x0 (@cons a0 x1 y0)) = False) x2.
Definition term15 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : a0 => fun y1 : list a0 => fun y2 : Prop => False) x0 x1.
Definition term22 (a0 : Type') (x0 : type1143 a0) (x1 : a0) := fun y0 : list a0 => (x0 (@cons a0 x1 y0)) = False.
Definition term23 (a0 : Type') (x0 : a0) (x1 : type1143 a0) := forall y0 : list a0, (x1 (@cons a0 x0 y0)) = ((fun y1 : a0 => fun y2 : list a0 => fun y3 : Prop => False) x0 y0 (x1 y0)).
Definition term40 (a0 : Type') := fun y0 : type1673 => fun y1 : type1143 a0 => ((y1 (@nil a0)) = True) /\ (forall y2 : a0, forall y3 : list a0, (y1 (@cons a0 y2 y3)) = False).
Definition term47 (a0 : Type') := fun y0 : type1673 => exists y1 : type1143 a0, ((y1 (@nil a0)) = True) /\ (forall y2 : a0, forall y3 : list a0, (y1 (@cons a0 y2 y3)) = False).
Definition term21 (a0 : Type') (x0 : a0) (x1 : type1143 a0) := fun y0 : list a0 => (x1 (@cons a0 x0 y0)) = ((fun y1 : a0 => fun y2 : list a0 => fun y3 : Prop => False) x0 y0 (x1 y0)).
Definition term60 (a0 : Type') := fun y0 : a0 -> Prop => y0 (@ε a0 y0).
Definition term50 (a0 : Type') (x0 : type1290 a0) (x1 : type1673) := (fun y0 : type1673 => fun y1 : type1143 a0 => ((y1 (@nil a0)) = True) /\ (forall y2 : a0, forall y3 : list a0, (y1 (@cons a0 y2 y3)) = False)) x1 (x0 x1).
Definition term62 (a0 : Type') := (fun y0 : type361 a0 => y0 (@ε ((prod nat (prod nat (prod nat nat))) -> (list a0) -> Prop) y0)) (fun y0 : type1290 a0 => forall y1 : type1673, ((y0 y1 (@nil a0)) = True) /\ (forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = False)).
Definition term20 (a0 : Type') (x0 : type1143 a0) (x1 : a0) (x2 : list a0) := @eq Prop (x0 (@cons a0 x1 x2)).
Definition term19 (a0 : Type') (x0 : type1143 a0) (x1 : list a0) := (fun y0 : Prop => False) (x0 x1).
Definition term45 (a0 : Type') (x0 : type1673) := exists y0 : type1143 a0, (fun y1 : type1673 => fun y2 : type1143 a0 => ((y2 (@nil a0)) = True) /\ (forall y3 : a0, forall y4 : list a0, (y2 (@cons a0 y3 y4)) = False)) x0 y0.
Definition term16 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => fun y1 : Prop => False) x0.
Definition term1 (a0 : Type') (x0 : type1143 a0) (x1 : a0) := (fun y0 : a0 => forall y1 : list a0, (x0 (@cons a0 y0 y1)) = False) x1.
Definition term31 (a0 : Type') := exists y0 : type1143 a0, ((y0 (@nil a0)) = True) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = False).
Definition term11 (a0 : Type') := exists y0 : type1143 a0, ((y0 (@nil a0)) = True) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = ((fun y3 : a0 => fun y4 : list a0 => fun y5 : Prop => False) y1 y2 (y0 y2))).
Definition term14 (a0 : Type') := fun y0 : list a0 => fun y1 : Prop => False.
Definition term53 (a0 : Type') (x0 : type1290 a0) := fun y0 : type1673 => (fun y1 : type1673 => fun y2 : type1143 a0 => ((y2 (@nil a0)) = True) /\ (forall y3 : a0, forall y4 : list a0, (y2 (@cons a0 y3 y4)) = False)) y0 (x0 y0).
Definition term0 (a0 : Type') (x0 : type1143 a0) := forall y0 : a0, forall y1 : list a0, (x0 (@cons a0 y0 y1)) = False.
Definition term42 (a0 : Type') (x0 : type1673) (x1 : type1143 a0) := (fun y0 : type1673 => fun y1 : type1143 a0 => ((y1 (@nil a0)) = True) /\ (forall y2 : a0, forall y3 : list a0, (y1 (@cons a0 y2 y3)) = False)) x0 x1.
Definition term17 := fun y0 : Prop => False.
Definition term7 (a0 : Type') (a1 : Type') (x0 : a1) := forall y0 : type1394 a0 a1, exists y1 : type1142 a0 a1, ((y1 (@nil a0)) = x0) /\ (forall y2 : a0, forall y3 : list a0, (y1 (@cons a0 y2 y3)) = (y0 y2 y3 (y1 y3))).
Definition term33 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => (forall y1 : a0, exists y2 : a1, y0 y1 y2) = (exists y1 : a0 -> a1, forall y2 : a0, y0 y2 (y1 y2))) x0.
Definition term41 (a0 : Type') (x0 : type1673) := (fun y0 : type1673 => fun y1 : type1143 a0 => ((y1 (@nil a0)) = True) /\ (forall y2 : a0, forall y3 : list a0, (y1 (@cons a0 y2 y3)) = False)) x0.
Definition term12 (a0 : Type') := fun y0 : a0 => fun y1 : list a0 => fun y2 : Prop => False.
Definition term18 (a0 : Type') (x0 : a0) (x1 : type1143 a0) (x2 : list a0) := (fun y0 : a0 => fun y1 : list a0 => fun y2 : Prop => False) x0 x2 (x1 x2).
Definition term44 (a0 : Type') (x0 : type1673) := fun y0 : type1143 a0 => (fun y1 : type1673 => fun y2 : type1143 a0 => ((y2 (@nil a0)) = True) /\ (forall y3 : a0, forall y4 : list a0, (y2 (@cons a0 y3 y4)) = False)) x0 y0.
Definition term43 (a0 : Type') (x0 : type1143 a0) := (fun y0 : type1143 a0 => ((y0 (@nil a0)) = True) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = False)) x0.
Definition term35 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term10 (a0 : Type') (x0 : Prop) (x1 : type1395 a0) := exists y0 : type1143 a0, ((y0 (@nil a0)) = x0) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = (x1 y1 y2 (y0 y2))).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1394 a0 a1) := exists y0 : type1142 a0 a1, ((y0 (@nil a0)) = x0) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = (x1 y1 y2 (y0 y2))).
Definition term38 (a0 : Type') := forall y0 : type1673, exists y1 : type1143 a0, (fun y2 : type1673 => fun y3 : type1143 a0 => ((y3 (@nil a0)) = True) /\ (forall y4 : a0, forall y5 : list a0, (y3 (@cons a0 y4 y5)) = False)) y0 y1.
Definition term36 (a0 : Type') (x0 : type1284 a0) := forall y0 : type1673, exists y1 : type1143 a0, x0 y0 y1.
Definition term26 (a0 : Type') (x0 : type1143 a0) := forall y0 : a0, forall y1 : list a0, (x0 (@cons a0 y0 y1)) = ((fun y2 : a0 => fun y3 : list a0 => fun y4 : Prop => False) y0 y1 (x0 y1)).
Definition term51 (a0 : Type') (x0 : type1290 a0) (x1 : type1673) := (fun y0 : type1143 a0 => ((y0 (@nil a0)) = True) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = False)) (x0 x1).
Definition term54 (a0 : Type') (x0 : type1290 a0) := fun y0 : type1673 => ((x0 y0 (@nil a0)) = True) /\ (forall y1 : a0, forall y2 : list a0, (x0 y0 (@cons a0 y1 y2)) = False).
Definition term27 (a0 : Type') (x0 : type1143 a0) := and ((x0 (@nil a0)) = True).
Definition term32 (a0 : Type') := forall y0 : type1673, exists y1 : type1143 a0, ((y1 (@nil a0)) = True) /\ (forall y2 : a0, forall y3 : list a0, (y1 (@cons a0 y2 y3)) = False).
Definition term46 (a0 : Type') := fun y0 : type1673 => exists y1 : type1143 a0, (fun y2 : type1673 => fun y3 : type1143 a0 => ((y3 (@nil a0)) = True) /\ (forall y4 : a0, forall y5 : list a0, (y3 (@cons a0 y4 y5)) = False)) y0 y1.
