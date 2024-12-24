Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term66 (a0 : Type') := fun y0 : type1322 a0 => forall y1 : prod nat nat, (forall y2 : list a0, (y0 y1 (NUMERAL 0) y2) = (@hd a0 y2)) /\ (forall y2 : nat, forall y3 : list a0, (y0 y1 (S y2) y3) = (y0 y1 y2 (@tl a0 y3))).
Definition term9 (a0 : Type') (x0 : type1587 a0) (x1 : nat) := fun y0 : list a0 => x0 x1 (@tl a0 y0).
Definition term57 (a0 : Type') := @eq Prop (forall y0 : prod nat nat, exists y1 : type1587 a0, (forall y2 : list a0, (y1 (NUMERAL 0) y2) = (@hd a0 y2)) /\ (forall y2 : nat, forall y3 : list a0, (y1 (S y2) y3) = (y1 y2 (@tl a0 y3)))).
Definition term56 (a0 : Type') := @eq Prop (forall y0 : prod nat nat, exists y1 : type1587 a0, (fun y2 : prod nat nat => fun y3 : type1587 a0 => (forall y4 : list a0, (y3 (NUMERAL 0) y4) = (@hd a0 y4)) /\ (forall y4 : nat, forall y5 : list a0, (y3 (S y4) y5) = (y3 y4 (@tl a0 y5)))) y0 y1).
Definition term65 (a0 : Type') := fun y0 : type1322 a0 => forall y1 : prod nat nat, (fun y2 : prod nat nat => fun y3 : type1587 a0 => (forall y4 : list a0, (y3 (NUMERAL 0) y4) = (@hd a0 y4)) /\ (forall y4 : nat, forall y5 : list a0, (y3 (S y4) y5) = (y3 y4 (@tl a0 y5)))) y1 (y0 y1).
Definition term52 (a0 : Type') (x0 : prod nat nat) := fun y0 : type1587 a0 => (fun y1 : prod nat nat => fun y2 : type1587 a0 => (forall y3 : list a0, (y2 (NUMERAL 0) y3) = (@hd a0 y3)) /\ (forall y3 : nat, forall y4 : list a0, (y2 (S y3) y4) = (y2 y3 (@tl a0 y4)))) x0 y0.
Definition term25 (a0 : Type') (x0 : type1587 a0) (x1 : nat) := (fun y0 : type1141 a0 => fun y1 : nat => fun y2 : list a0 => y0 (@tl a0 y2)) (x0 x1).
Definition term6 (a0 : Type') (x0 : type1587 a0) := forall y0 : nat, (x0 (S y0)) = (fun y1 : list a0 => x0 y0 (@tl a0 y1)).
Definition term50 (a0 : Type') (x0 : prod nat nat) (x1 : type1587 a0) := (fun y0 : prod nat nat => fun y1 : type1587 a0 => (forall y2 : list a0, (y1 (NUMERAL 0) y2) = (@hd a0 y2)) /\ (forall y2 : nat, forall y3 : list a0, (y1 (S y2) y3) = (y1 y2 (@tl a0 y3)))) x0 x1.
Definition term34 (a0 : Type') (x0 : type1587 a0) := ((x0 (NUMERAL 0)) = (fun y0 : list a0 => @hd a0 y0)) /\ (forall y0 : nat, (x0 (S y0)) = ((fun y1 : type1141 a0 => fun y2 : nat => fun y3 : list a0 => y1 (@tl a0 y3)) (x0 y0) y0)).
Definition term20 (a0 : Type') (x0 : a0) (x1 : type1423 a0) := (fun y0 : type1423 a0 => exists y1 : nat -> a0, ((y1 (NUMERAL 0)) = x0) /\ (forall y2 : nat, (y1 (S y2)) = (y0 (y1 y2) y2))) x1.
Definition term27 (a0 : Type') (x0 : type1587 a0) (x1 : nat) := (fun y0 : type1141 a0 => fun y1 : nat => fun y2 : list a0 => y0 (@tl a0 y2)) (x0 x1) x1.
Definition term71 (a0 : Type') := (fun y0 : type1322 a0 => forall y1 : prod nat nat, (forall y2 : list a0, (y0 y1 (NUMERAL 0) y2) = (@hd a0 y2)) /\ (forall y2 : nat, forall y3 : list a0, (y0 y1 (S y2) y3) = (y0 y1 y2 (@tl a0 y3)))) (@ε ((prod nat nat) -> nat -> (list a0) -> a0) (fun y0 : type1322 a0 => forall y1 : prod nat nat, (forall y2 : list a0, (y0 y1 (NUMERAL 0) y2) = (@hd a0 y2)) /\ (forall y2 : nat, forall y3 : list a0, (y0 y1 (S y2) y3) = (y0 y1 y2 (@tl a0 y3))))).
Definition term59 (a0 : Type') (x0 : type1322 a0) (x1 : prod nat nat) := (fun y0 : type1587 a0 => (forall y1 : list a0, (y0 (NUMERAL 0) y1) = (@hd a0 y1)) /\ (forall y1 : nat, forall y2 : list a0, (y0 (S y1) y2) = (y0 y1 (@tl a0 y2)))) (x0 x1).
Definition term64 (a0 : Type') (x0 : type1322 a0) := forall y0 : prod nat nat, (forall y1 : list a0, (x0 y0 (NUMERAL 0) y1) = (@hd a0 y1)) /\ (forall y1 : nat, forall y2 : list a0, (x0 y0 (S y1) y2) = (x0 y0 y1 (@tl a0 y2))).
Definition term38 (a0 : Type') := exists y0 : type1587 a0, (forall y1 : list a0, (y0 (NUMERAL 0) y1) = (@hd a0 y1)) /\ (forall y1 : nat, forall y2 : list a0, (y0 (S y1) y2) = (y0 y1 (@tl a0 y2))).
Definition term32 (a0 : Type') (x0 : type1587 a0) := forall y0 : nat, (x0 (S y0)) = ((fun y1 : type1141 a0 => fun y2 : nat => fun y3 : list a0 => y1 (@tl a0 y3)) (x0 y0) y0).
Definition term55 (a0 : Type') := fun y0 : prod nat nat => exists y1 : type1587 a0, (forall y2 : list a0, (y1 (NUMERAL 0) y2) = (@hd a0 y2)) /\ (forall y2 : nat, forall y3 : list a0, (y1 (S y2) y3) = (y1 y2 (@tl a0 y3))).
Definition term5 (a0 : Type') (x0 : type1587 a0) := forall y0 : list a0, (x0 (NUMERAL 0) y0) = (@hd a0 y0).
Definition term42 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term67 (a0 : Type') := exists y0 : type1322 a0, forall y1 : prod nat nat, (forall y2 : list a0, (y0 y1 (NUMERAL 0) y2) = (@hd a0 y2)) /\ (forall y2 : nat, forall y3 : list a0, (y0 y1 (S y2) y3) = (y0 y1 y2 (@tl a0 y3))).
Definition term47 (a0 : Type') := exists y0 : type1322 a0, forall y1 : prod nat nat, (fun y2 : prod nat nat => fun y3 : type1587 a0 => (forall y4 : list a0, (y3 (NUMERAL 0) y4) = (@hd a0 y4)) /\ (forall y4 : nat, forall y5 : list a0, (y3 (S y4) y5) = (y3 y4 (@tl a0 y5)))) y1 (y0 y1).
Definition term45 (a0 : Type') (x0 : type1318 a0) := exists y0 : type1322 a0, forall y1 : prod nat nat, x0 y1 (y0 y1).
Definition term63 (a0 : Type') (x0 : type1322 a0) := forall y0 : prod nat nat, (fun y1 : prod nat nat => fun y2 : type1587 a0 => (forall y3 : list a0, (y2 (NUMERAL 0) y3) = (@hd a0 y3)) /\ (forall y3 : nat, forall y4 : list a0, (y2 (S y3) y4) = (y2 y3 (@tl a0 y4)))) y0 (x0 y0).
Definition term26 (a0 : Type') (x0 : type1587 a0) (x1 : nat) := fun y0 : nat => fun y1 : list a0 => x0 x1 (@tl a0 y1).
Definition term69 (a0 : Type') := fun y0 : type379 a0 => y0 (@ε ((prod nat nat) -> nat -> (list a0) -> a0) y0).
Definition term30 (a0 : Type') (x0 : type1587 a0) := fun y0 : nat => (x0 (S y0)) = ((fun y1 : type1141 a0 => fun y2 : nat => fun y3 : list a0 => y1 (@tl a0 y3)) (x0 y0) y0).
Definition term18 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : type1423 a0, exists y2 : nat -> a0, ((y2 (NUMERAL 0)) = y0) /\ (forall y3 : nat, (y2 (S y3)) = (y1 (y2 y3) y3))) x0.
Definition term4 (a0 : Type') (x0 : type1587 a0) (x1 : list a0) := @eq a0 (x0 (NUMERAL 0) x1).
Definition term37 (a0 : Type') := exists y0 : type1587 a0, ((y0 (NUMERAL 0)) = (fun y1 : list a0 => @hd a0 y1)) /\ (forall y1 : nat, (y0 (S y1)) = (fun y2 : list a0 => y0 y1 (@tl a0 y2))).
Definition term23 (a0 : Type') := exists y0 : type1587 a0, ((y0 (NUMERAL 0)) = (fun y1 : list a0 => @hd a0 y1)) /\ (forall y1 : nat, (y0 (S y1)) = ((fun y2 : type1141 a0 => fun y3 : nat => fun y4 : list a0 => y2 (@tl a0 y4)) (y0 y1) y1)).
Definition term68 (a0 : Type') := fun y0 : a0 -> Prop => y0 (@ε a0 y0).
Definition term58 (a0 : Type') (x0 : type1322 a0) (x1 : prod nat nat) := (fun y0 : prod nat nat => fun y1 : type1587 a0 => (forall y2 : list a0, (y1 (NUMERAL 0) y2) = (@hd a0 y2)) /\ (forall y2 : nat, forall y3 : list a0, (y1 (S y2) y3) = (y1 y2 (@tl a0 y3)))) x1 (x0 x1).
Definition term70 (a0 : Type') := (fun y0 : type379 a0 => y0 (@ε ((prod nat nat) -> nat -> (list a0) -> a0) y0)) (fun y0 : type1322 a0 => forall y1 : prod nat nat, (forall y2 : list a0, (y0 y1 (NUMERAL 0) y2) = (@hd a0 y2)) /\ (forall y2 : nat, forall y3 : list a0, (y0 y1 (S y2) y3) = (y0 y1 y2 (@tl a0 y3)))).
Definition term15 (a0 : Type') (x0 : type1587 a0) := forall y0 : nat, forall y1 : list a0, (x0 (S y0) y1) = (x0 y0 (@tl a0 y1)).
Definition term62 (a0 : Type') (x0 : type1322 a0) := fun y0 : prod nat nat => (forall y1 : list a0, (x0 y0 (NUMERAL 0) y1) = (@hd a0 y1)) /\ (forall y1 : nat, forall y2 : list a0, (x0 y0 (S y1) y2) = (x0 y0 y1 (@tl a0 y2))).
Definition term31 (a0 : Type') (x0 : type1587 a0) := fun y0 : nat => (x0 (S y0)) = (fun y1 : list a0 => x0 y0 (@tl a0 y1)).
Definition term12 (a0 : Type') (x0 : type1587 a0) (x1 : nat) (x2 : list a0) := x0 x1 (@tl a0 x2).
Definition term28 (a0 : Type') (x0 : type1587 a0) (x1 : nat) := (fun y0 : nat => fun y1 : list a0 => x0 x1 (@tl a0 y1)) x1.
Definition term53 (a0 : Type') (x0 : prod nat nat) := exists y0 : type1587 a0, (fun y1 : prod nat nat => fun y2 : type1587 a0 => (forall y3 : list a0, (y2 (NUMERAL 0) y3) = (@hd a0 y3)) /\ (forall y3 : nat, forall y4 : list a0, (y2 (S y3) y4) = (y2 y3 (@tl a0 y4)))) x0 y0.
Definition term39 (a0 : Type') := fun y0 : type1587 a0 => (forall y1 : list a0, (y0 (NUMERAL 0) y1) = (@hd a0 y1)) /\ (forall y1 : nat, forall y2 : list a0, (y0 (S y1) y2) = (y0 y1 (@tl a0 y2))).
Definition term51 (a0 : Type') (x0 : type1587 a0) := (fun y0 : type1587 a0 => (forall y1 : list a0, (y0 (NUMERAL 0) y1) = (@hd a0 y1)) /\ (forall y1 : nat, forall y2 : list a0, (y0 (S y1) y2) = (y0 y1 (@tl a0 y2)))) x0.
Definition term24 (a0 : Type') := fun y0 : type1141 a0 => fun y1 : nat => fun y2 : list a0 => y0 (@tl a0 y2).
Definition term3 (a0 : Type') (x0 : list a0) := (fun y0 : list a0 => @hd a0 y0) x0.
Definition term60 (a0 : Type') (x0 : type1322 a0) (x1 : prod nat nat) := (forall y0 : list a0, (x0 x1 (NUMERAL 0) y0) = (@hd a0 y0)) /\ (forall y0 : nat, forall y1 : list a0, (x0 x1 (S y0) y1) = (x0 x1 y0 (@tl a0 y1))).
Definition term17 (a0 : Type') (x0 : type1587 a0) := (forall y0 : list a0, (x0 (NUMERAL 0) y0) = (@hd a0 y0)) /\ (forall y0 : nat, forall y1 : list a0, (x0 (S y0) y1) = (x0 y0 (@tl a0 y1))).
Definition term61 (a0 : Type') (x0 : type1322 a0) := fun y0 : prod nat nat => (fun y1 : prod nat nat => fun y2 : type1587 a0 => (forall y3 : list a0, (y2 (NUMERAL 0) y3) = (@hd a0 y3)) /\ (forall y3 : nat, forall y4 : list a0, (y2 (S y3) y4) = (y2 y3 (@tl a0 y4)))) y0 (x0 y0).
Definition term0 (a0 : Type') (x0 : type1587 a0) := x0 (NUMERAL 0).
Definition term29 (a0 : Type') (x0 : type1587 a0) (x1 : nat) := @eq ((list a0) -> a0) (x0 (S x1)).
Definition term48 (a0 : Type') := fun y0 : prod nat nat => fun y1 : type1587 a0 => (forall y2 : list a0, (y1 (NUMERAL 0) y2) = (@hd a0 y2)) /\ (forall y2 : nat, forall y3 : list a0, (y1 (S y2) y3) = (y1 y2 (@tl a0 y3))).
Definition term36 (a0 : Type') := fun y0 : type1587 a0 => ((y0 (NUMERAL 0)) = (fun y1 : list a0 => @hd a0 y1)) /\ (forall y1 : nat, (y0 (S y1)) = (fun y2 : list a0 => y0 y1 (@tl a0 y2))).
Definition term35 (a0 : Type') := fun y0 : type1587 a0 => ((y0 (NUMERAL 0)) = (fun y1 : list a0 => @hd a0 y1)) /\ (forall y1 : nat, (y0 (S y1)) = ((fun y2 : type1141 a0 => fun y3 : nat => fun y4 : list a0 => y2 (@tl a0 y4)) (y0 y1) y1)).
Definition term1 (a0 : Type') := fun y0 : list a0 => @hd a0 y0.
Definition term11 (a0 : Type') (x0 : type1587 a0) (x1 : nat) (x2 : list a0) := (fun y0 : list a0 => x0 x1 (@tl a0 y0)) x2.
Definition term8 (a0 : Type') (x0 : type1587 a0) (x1 : nat) := x0 (S x1).
Definition term19 (a0 : Type') (x0 : a0) := forall y0 : type1423 a0, exists y1 : nat -> a0, ((y1 (NUMERAL 0)) = x0) /\ (forall y2 : nat, (y1 (S y2)) = (y0 (y1 y2) y2)).
Definition term41 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => (forall y1 : a0, exists y2 : a1, y0 y1 y2) = (exists y1 : a0 -> a1, forall y2 : a0, y0 y2 (y1 y2))) x0.
Definition term49 (a0 : Type') (x0 : prod nat nat) := (fun y0 : prod nat nat => fun y1 : type1587 a0 => (forall y2 : list a0, (y1 (NUMERAL 0) y2) = (@hd a0 y2)) /\ (forall y2 : nat, forall y3 : list a0, (y1 (S y2) y3) = (y1 y2 (@tl a0 y3)))) x0.
Definition term16 (a0 : Type') (x0 : type1587 a0) := ((x0 (NUMERAL 0)) = (fun y0 : list a0 => @hd a0 y0)) /\ (forall y0 : nat, (x0 (S y0)) = (fun y1 : list a0 => x0 y0 (@tl a0 y1))).
Definition term14 (a0 : Type') (x0 : type1587 a0) (x1 : nat) := forall y0 : list a0, (x0 (S x1) y0) = (x0 x1 (@tl a0 y0)).
Definition term7 (a0 : Type') (x0 : type1587 a0) (x1 : nat) := (fun y0 : nat => (x0 (S y0)) = (fun y1 : list a0 => x0 y0 (@tl a0 y1))) x1.
Definition term43 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term22 (a0 : Type') (x0 : type1141 a0) (x1 : type276 a0) := exists y0 : type1587 a0, ((y0 (NUMERAL 0)) = x0) /\ (forall y1 : nat, (y0 (S y1)) = (x1 (y0 y1) y1)).
Definition term21 (a0 : Type') (x0 : a0) (x1 : type1423 a0) := exists y0 : nat -> a0, ((y0 (NUMERAL 0)) = x0) /\ (forall y1 : nat, (y0 (S y1)) = (x1 (y0 y1) y1)).
Definition term46 (a0 : Type') := forall y0 : prod nat nat, exists y1 : type1587 a0, (fun y2 : prod nat nat => fun y3 : type1587 a0 => (forall y4 : list a0, (y3 (NUMERAL 0) y4) = (@hd a0 y4)) /\ (forall y4 : nat, forall y5 : list a0, (y3 (S y4) y5) = (y3 y4 (@tl a0 y5)))) y0 y1.
Definition term44 (a0 : Type') (x0 : type1318 a0) := forall y0 : prod nat nat, exists y1 : type1587 a0, x0 y0 y1.
Definition term13 (a0 : Type') (x0 : type1587 a0) (x1 : nat) (x2 : list a0) := @eq a0 (x0 (S x1) x2).
Definition term2 (a0 : Type') (x0 : type1587 a0) (x1 : list a0) := x0 (NUMERAL 0) x1.
Definition term40 (a0 : Type') := forall y0 : prod nat nat, exists y1 : type1587 a0, (forall y2 : list a0, (y1 (NUMERAL 0) y2) = (@hd a0 y2)) /\ (forall y2 : nat, forall y3 : list a0, (y1 (S y2) y3) = (y1 y2 (@tl a0 y3))).
Definition term33 (a0 : Type') (x0 : type1587 a0) := and ((x0 (NUMERAL 0)) = (fun y0 : list a0 => @hd a0 y0)).
Definition term10 (a0 : Type') (x0 : type1587 a0) (x1 : nat) (x2 : list a0) := x0 (S x1) x2.
Definition term54 (a0 : Type') := fun y0 : prod nat nat => exists y1 : type1587 a0, (fun y2 : prod nat nat => fun y3 : type1587 a0 => (forall y4 : list a0, (y3 (NUMERAL 0) y4) = (@hd a0 y4)) /\ (forall y4 : nat, forall y5 : list a0, (y3 (S y4) y5) = (y3 y4 (@tl a0 y5)))) y0 y1.
