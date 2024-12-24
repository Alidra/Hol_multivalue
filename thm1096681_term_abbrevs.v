Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term57 (a0 : Type') (x0 : type1271 a0) := forall y0 : type1671, ((x0 y0 (@nil a0)) = (NUMERAL 0)) /\ (forall y1 : a0, forall y2 : list a0, (x0 y0 (@cons a0 y1 y2)) = (S (x0 y0 y2))).
Definition term59 (a0 : Type') := fun y0 : type1271 a0 => forall y1 : type1671, ((y0 y1 (@nil a0)) = (NUMERAL 0)) /\ (forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = (S (y0 y1 y3))).
Definition term50 (a0 : Type') := @eq Prop (forall y0 : type1671, exists y1 : type1144 a0, ((y1 (@nil a0)) = (NUMERAL 0)) /\ (forall y2 : a0, forall y3 : list a0, (y1 (@cons a0 y2 y3)) = (S (y1 y3)))).
Definition term49 (a0 : Type') := @eq Prop (forall y0 : type1671, exists y1 : type1144 a0, (fun y2 : type1671 => fun y3 : type1144 a0 => ((y3 (@nil a0)) = (NUMERAL 0)) /\ (forall y4 : a0, forall y5 : list a0, (y3 (@cons a0 y4 y5)) = (S (y3 y5)))) y0 y1).
Definition term58 (a0 : Type') := fun y0 : type1271 a0 => forall y1 : type1671, (fun y2 : type1671 => fun y3 : type1144 a0 => ((y3 (@nil a0)) = (NUMERAL 0)) /\ (forall y4 : a0, forall y5 : list a0, (y3 (@cons a0 y4 y5)) = (S (y3 y5)))) y1 (y0 y1).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a1) := (fun y0 : a1 => forall y1 : type1394 a0 a1, exists y2 : type1142 a0 a1, ((y2 (@nil a0)) = y0) /\ (forall y3 : a0, forall y4 : list a0, (y2 (@cons a0 y3 y4)) = (y1 y3 y4 (y2 y4)))) x0.
Definition term25 (a0 : Type') (x0 : type1144 a0) := fun y0 : a0 => forall y1 : list a0, (x0 (@cons a0 y0 y1)) = ((fun y2 : a0 => fun y3 : list a0 => fun y4 : nat => S y4) y0 y1 (x0 y1)).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1394 a0 a1) := (fun y0 : type1394 a0 a1 => exists y1 : type1142 a0 a1, ((y1 (@nil a0)) = x0) /\ (forall y2 : a0, forall y3 : list a0, (y1 (@cons a0 y2 y3)) = (y0 y2 y3 (y1 y3)))) x1.
Definition term64 (a0 : Type') := (fun y0 : type1271 a0 => forall y1 : type1671, ((y0 y1 (@nil a0)) = (NUMERAL 0)) /\ (forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = (S (y0 y1 y3)))) (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (list a0) -> nat) (fun y0 : type1271 a0 => forall y1 : type1671, ((y0 y1 (@nil a0)) = (NUMERAL 0)) /\ (forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = (S (y0 y1 y3))))).
Definition term26 (a0 : Type') (x0 : type1144 a0) := fun y0 : a0 => forall y1 : list a0, (x0 (@cons a0 y0 y1)) = (S (x0 y1)).
Definition term4 (a0 : Type') (x0 : type1144 a0) (x1 : a0) (x2 : list a0) := x0 (@cons a0 x1 x2).
Definition term35 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term1 (a0 : Type') (x0 : type1144 a0) (x1 : a0) := (fun y0 : a0 => forall y1 : list a0, (x0 (@cons a0 y0 y1)) = (S (x0 y1))) x1.
Definition term60 (a0 : Type') := exists y0 : type1271 a0, forall y1 : type1671, ((y0 y1 (@nil a0)) = (NUMERAL 0)) /\ (forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = (S (y0 y1 y3))).
Definition term40 (a0 : Type') := exists y0 : type1271 a0, forall y1 : type1671, (fun y2 : type1671 => fun y3 : type1144 a0 => ((y3 (@nil a0)) = (NUMERAL 0)) /\ (forall y4 : a0, forall y5 : list a0, (y3 (@cons a0 y4 y5)) = (S (y3 y5)))) y1 (y0 y1).
Definition term38 (a0 : Type') (x0 : type1265 a0) := exists y0 : type1271 a0, forall y1 : type1671, x0 y1 (y0 y1).
Definition term56 (a0 : Type') (x0 : type1271 a0) := forall y0 : type1671, (fun y1 : type1671 => fun y2 : type1144 a0 => ((y2 (@nil a0)) = (NUMERAL 0)) /\ (forall y3 : a0, forall y4 : list a0, (y2 (@cons a0 y3 y4)) = (S (y2 y4)))) y0 (x0 y0).
Definition term62 (a0 : Type') := fun y0 : type352 a0 => y0 (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (list a0) -> nat) y0).
Definition term32 (a0 : Type') := exists y0 : type1144 a0, ((y0 (@nil a0)) = (NUMERAL 0)) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = (S (y0 y2))).
Definition term12 (a0 : Type') := exists y0 : type1144 a0, ((y0 (@nil a0)) = (NUMERAL 0)) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = ((fun y3 : a0 => fun y4 : list a0 => fun y5 : nat => S y5) y1 y2 (y0 y2))).
Definition term24 (a0 : Type') (x0 : a0) (x1 : type1144 a0) := forall y0 : list a0, (x1 (@cons a0 x0 y0)) = ((fun y1 : a0 => fun y2 : list a0 => fun y3 : nat => S y3) x0 y0 (x1 y0)).
Definition term48 (a0 : Type') := fun y0 : type1671 => exists y1 : type1144 a0, ((y1 (@nil a0)) = (NUMERAL 0)) /\ (forall y2 : a0, forall y3 : list a0, (y1 (@cons a0 y2 y3)) = (S (y1 y3))).
Definition term22 (a0 : Type') (x0 : a0) (x1 : type1144 a0) := fun y0 : list a0 => (x1 (@cons a0 x0 y0)) = ((fun y1 : a0 => fun y2 : list a0 => fun y3 : nat => S y3) x0 y0 (x1 y0)).
Definition term20 (a0 : Type') (x0 : type1144 a0) (x1 : list a0) := (fun y0 : nat => S y0) (x0 x1).
Definition term61 (a0 : Type') := fun y0 : a0 -> Prop => y0 (@ε a0 y0).
Definition term23 (a0 : Type') (x0 : a0) (x1 : type1144 a0) := fun y0 : list a0 => (x1 (@cons a0 x0 y0)) = (S (x1 y0)).
Definition term51 (a0 : Type') (x0 : type1271 a0) (x1 : type1671) := (fun y0 : type1671 => fun y1 : type1144 a0 => ((y1 (@nil a0)) = (NUMERAL 0)) /\ (forall y2 : a0, forall y3 : list a0, (y1 (@cons a0 y2 y3)) = (S (y1 y3)))) x1 (x0 x1).
Definition term29 (a0 : Type') (x0 : type1144 a0) := ((x0 (@nil a0)) = (NUMERAL 0)) /\ (forall y0 : a0, forall y1 : list a0, (x0 (@cons a0 y0 y1)) = ((fun y2 : a0 => fun y3 : list a0 => fun y4 : nat => S y4) y0 y1 (x0 y1))).
Definition term6 (a0 : Type') (x0 : type1144 a0) := ((x0 (@nil a0)) = (NUMERAL 0)) /\ (forall y0 : a0, forall y1 : list a0, (x0 (@cons a0 y0 y1)) = (S (x0 y1))).
Definition term63 (a0 : Type') := (fun y0 : type352 a0 => y0 (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat nat))))) -> (list a0) -> nat) y0)) (fun y0 : type1271 a0 => forall y1 : type1671, ((y0 y1 (@nil a0)) = (NUMERAL 0)) /\ (forall y2 : a0, forall y3 : list a0, (y0 y1 (@cons a0 y2 y3)) = (S (y0 y1 y3)))).
Definition term16 (a0 : Type') (x0 : a0) (x1 : list a0) := (fun y0 : a0 => fun y1 : list a0 => fun y2 : nat => S y2) x0 x1.
Definition term46 (a0 : Type') (x0 : type1671) := exists y0 : type1144 a0, (fun y1 : type1671 => fun y2 : type1144 a0 => ((y2 (@nil a0)) = (NUMERAL 0)) /\ (forall y3 : a0, forall y4 : list a0, (y2 (@cons a0 y3 y4)) = (S (y2 y4)))) x0 y0.
Definition term55 (a0 : Type') (x0 : type1271 a0) := fun y0 : type1671 => ((x0 y0 (@nil a0)) = (NUMERAL 0)) /\ (forall y1 : a0, forall y2 : list a0, (x0 y0 (@cons a0 y1 y2)) = (S (x0 y0 y2))).
Definition term53 (a0 : Type') (x0 : type1271 a0) (x1 : type1671) := ((x0 x1 (@nil a0)) = (NUMERAL 0)) /\ (forall y0 : a0, forall y1 : list a0, (x0 x1 (@cons a0 y0 y1)) = (S (x0 x1 y1))).
Definition term14 (a0 : Type') (x0 : a0) := (fun y0 : a0 => fun y1 : list a0 => fun y2 : nat => S y2) x0.
Definition term13 (a0 : Type') := fun y0 : a0 => fun y1 : list a0 => fun y2 : nat => S y2.
Definition term28 (a0 : Type') (x0 : type1144 a0) := and ((x0 (@nil a0)) = (NUMERAL 0)).
Definition term54 (a0 : Type') (x0 : type1271 a0) := fun y0 : type1671 => (fun y1 : type1671 => fun y2 : type1144 a0 => ((y2 (@nil a0)) = (NUMERAL 0)) /\ (forall y3 : a0, forall y4 : list a0, (y2 (@cons a0 y3 y4)) = (S (y2 y4)))) y0 (x0 y0).
Definition term31 (a0 : Type') := fun y0 : type1144 a0 => ((y0 (@nil a0)) = (NUMERAL 0)) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = (S (y0 y2))).
Definition term30 (a0 : Type') := fun y0 : type1144 a0 => ((y0 (@nil a0)) = (NUMERAL 0)) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = ((fun y3 : a0 => fun y4 : list a0 => fun y5 : nat => S y5) y1 y2 (y0 y2))).
Definition term2 (a0 : Type') (x0 : a0) (x1 : type1144 a0) := forall y0 : list a0, (x1 (@cons a0 x0 y0)) = (S (x1 y0)).
Definition term3 (a0 : Type') (x0 : a0) (x1 : type1144 a0) (x2 : list a0) := (fun y0 : list a0 => (x1 (@cons a0 x0 y0)) = (S (x1 y0))) x2.
Definition term52 (a0 : Type') (x0 : type1271 a0) (x1 : type1671) := (fun y0 : type1144 a0 => ((y0 (@nil a0)) = (NUMERAL 0)) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = (S (y0 y2)))) (x0 x1).
Definition term18 := fun y0 : nat => S y0.
Definition term43 (a0 : Type') (x0 : type1671) (x1 : type1144 a0) := (fun y0 : type1671 => fun y1 : type1144 a0 => ((y1 (@nil a0)) = (NUMERAL 0)) /\ (forall y2 : a0, forall y3 : list a0, (y1 (@cons a0 y2 y3)) = (S (y1 y3)))) x0 x1.
Definition term15 (a0 : Type') := fun y0 : list a0 => fun y1 : nat => S y1.
Definition term17 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => fun y1 : nat => S y1) x0.
Definition term8 (a0 : Type') (a1 : Type') (x0 : a1) := forall y0 : type1394 a0 a1, exists y1 : type1142 a0 a1, ((y1 (@nil a0)) = x0) /\ (forall y2 : a0, forall y3 : list a0, (y1 (@cons a0 y2 y3)) = (y0 y2 y3 (y1 y3))).
Definition term34 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => (forall y1 : a0, exists y2 : a1, y0 y1 y2) = (exists y1 : a0 -> a1, forall y2 : a0, y0 y2 (y1 y2))) x0.
Definition term42 (a0 : Type') (x0 : type1671) := (fun y0 : type1671 => fun y1 : type1144 a0 => ((y1 (@nil a0)) = (NUMERAL 0)) /\ (forall y2 : a0, forall y3 : list a0, (y1 (@cons a0 y2 y3)) = (S (y1 y3)))) x0.
Definition term19 (a0 : Type') (x0 : a0) (x1 : type1144 a0) (x2 : list a0) := (fun y0 : a0 => fun y1 : list a0 => fun y2 : nat => S y2) x0 x2 (x1 x2).
Definition term45 (a0 : Type') (x0 : type1671) := fun y0 : type1144 a0 => (fun y1 : type1671 => fun y2 : type1144 a0 => ((y2 (@nil a0)) = (NUMERAL 0)) /\ (forall y3 : a0, forall y4 : list a0, (y2 (@cons a0 y3 y4)) = (S (y2 y4)))) x0 y0.
Definition term5 (a0 : Type') (x0 : type1144 a0) (x1 : list a0) := S (x0 x1).
Definition term36 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term11 (a0 : Type') (x0 : nat) (x1 : type1396 a0) := exists y0 : type1144 a0, ((y0 (@nil a0)) = x0) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = (x1 y1 y2 (y0 y2))).
Definition term10 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : type1394 a0 a1) := exists y0 : type1142 a0 a1, ((y0 (@nil a0)) = x0) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = (x1 y1 y2 (y0 y2))).
Definition term39 (a0 : Type') := forall y0 : type1671, exists y1 : type1144 a0, (fun y2 : type1671 => fun y3 : type1144 a0 => ((y3 (@nil a0)) = (NUMERAL 0)) /\ (forall y4 : a0, forall y5 : list a0, (y3 (@cons a0 y4 y5)) = (S (y3 y5)))) y0 y1.
Definition term37 (a0 : Type') (x0 : type1265 a0) := forall y0 : type1671, exists y1 : type1144 a0, x0 y0 y1.
Definition term27 (a0 : Type') (x0 : type1144 a0) := forall y0 : a0, forall y1 : list a0, (x0 (@cons a0 y0 y1)) = ((fun y2 : a0 => fun y3 : list a0 => fun y4 : nat => S y4) y0 y1 (x0 y1)).
Definition term0 (a0 : Type') (x0 : type1144 a0) := forall y0 : a0, forall y1 : list a0, (x0 (@cons a0 y0 y1)) = (S (x0 y1)).
Definition term33 (a0 : Type') := forall y0 : type1671, exists y1 : type1144 a0, ((y1 (@nil a0)) = (NUMERAL 0)) /\ (forall y2 : a0, forall y3 : list a0, (y1 (@cons a0 y2 y3)) = (S (y1 y3))).
Definition term44 (a0 : Type') (x0 : type1144 a0) := (fun y0 : type1144 a0 => ((y0 (@nil a0)) = (NUMERAL 0)) /\ (forall y1 : a0, forall y2 : list a0, (y0 (@cons a0 y1 y2)) = (S (y0 y2)))) x0.
Definition term41 (a0 : Type') := fun y0 : type1671 => fun y1 : type1144 a0 => ((y1 (@nil a0)) = (NUMERAL 0)) /\ (forall y2 : a0, forall y3 : list a0, (y1 (@cons a0 y2 y3)) = (S (y1 y3))).
Definition term21 (a0 : Type') (x0 : type1144 a0) (x1 : a0) (x2 : list a0) := @eq nat (x0 (@cons a0 x1 x2)).
Definition term47 (a0 : Type') := fun y0 : type1671 => exists y1 : type1144 a0, (fun y2 : type1671 => fun y3 : type1144 a0 => ((y3 (@nil a0)) = (NUMERAL 0)) /\ (forall y4 : a0, forall y5 : list a0, (y3 (@cons a0 y4 y5)) = (S (y3 y5)))) y0 y1.
