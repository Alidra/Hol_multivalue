Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0, ((fun y2 : a0 => y0 y2) y1) = (y0 y1)) x0.
Definition term107 (x0 : type1602) := fun y0 : nat => (fun y1 : nat => fun y2 : type1606 => (forall y3 : nat, (y2 y3 (NUMERAL 0)) = y3) /\ (forall y3 : nat, forall y4 : nat, (y2 y3 (S y4)) = (Nat.pred (y2 y3 y4)))) y0 (x0 y0).
Definition term70 (x0 : type1606) (x1 : nat) := (fun y0 : nat => fun y1 : nat => Nat.pred (x0 x1 y1)) x1.
Definition term29 (x0 : type1606) (x1 : nat) (x2 : nat) := x0 x1 (S x2).
Definition term67 (x0 : type1606) (x1 : nat) := (fun y0 : nat -> nat => fun y1 : nat => fun y2 : nat => Nat.pred (y0 y2)) (x0 x1).
Definition term4 (x0 : type1606) := fun y0 : nat => fun y1 : nat => x0 y1 y0.
Definition term40 (x0 : type1606) (x1 : nat) (x2 : nat) := Nat.pred (x0 x1 x2).
Definition term92 := forall y0 : nat, exists y1 : type1606, (fun y2 : nat => fun y3 : type1606 => (forall y4 : nat, (y3 y4 (NUMERAL 0)) = y4) /\ (forall y4 : nat, forall y5 : nat, (y3 y4 (S y5)) = (Nat.pred (y3 y4 y5)))) y0 y1.
Definition term90 (x0 : type1581) := forall y0 : nat, exists y1 : type1606, x0 y0 y1.
Definition term86 := forall y0 : nat, exists y1 : type1606, (forall y2 : nat, (y1 y2 (NUMERAL 0)) = y2) /\ (forall y2 : nat, forall y3 : nat, (y1 y2 (S y3)) = (Nat.pred (y1 y2 y3))).
Definition term11 (x0 : type1606) (x1 : nat) := @eq (nat -> nat) ((fun y0 : nat => fun y1 : nat => x0 y1 y0) x1).
Definition term17 (x0 : type1606) (x1 : nat) := fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0, ((fun y1 : a0 => x0 y1) y0) = (x0 y0).
Definition term57 (x0 : type1606) (x1 : nat) := fun y0 : nat => Nat.pred (x0 x1 y0).
Definition term9 (x0 : type1606) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => x0 y2 y1) y0.
Definition term62 (a0 : Type') (x0 : a0) (x1 : type1423 a0) := (fun y0 : type1423 a0 => exists y1 : nat -> a0, ((y1 (NUMERAL 0)) = x0) /\ (forall y2 : nat, (y1 (S y2)) = (y0 (y1 y2) y2))) x1.
Definition term69 (x0 : type1606) (x1 : nat) := (fun y0 : nat -> nat => fun y1 : nat => fun y2 : nat => Nat.pred (y0 y2)) (x0 x1) x1.
Definition term42 (x0 : type1606) (x1 : nat) := fun y0 : nat => (x0 (S y0) x1) = (Nat.pred (x0 y0 x1)).
Definition term108 (x0 : type1602) := fun y0 : nat => (forall y1 : nat, (x0 y0 y1 (NUMERAL 0)) = y1) /\ (forall y1 : nat, forall y2 : nat, (x0 y0 y1 (S y2)) = (Nat.pred (x0 y0 y1 y2))).
Definition term15 (x0 : type1606) (x1 : nat) := (fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) (NUMERAL 0).
Definition term117 := (fun y0 : type1602 => forall y1 : nat, (forall y2 : nat, (y0 y1 y2 (NUMERAL 0)) = y2) /\ (forall y2 : nat, forall y3 : nat, (y0 y1 y2 (S y3)) = (Nat.pred (y0 y1 y2 y3)))) (@ε (nat -> nat -> nat -> nat) (fun y0 : type1602 => forall y1 : nat, (forall y2 : nat, (y0 y1 y2 (NUMERAL 0)) = y2) /\ (forall y2 : nat, forall y3 : nat, (y0 y1 y2 (S y3)) = (Nat.pred (y0 y1 y2 y3))))).
Definition term82 := exists y0 : type1606, (forall y1 : nat, (y0 y1 (NUMERAL 0)) = y1) /\ (forall y1 : nat, forall y2 : nat, (y0 y1 (S y2)) = (Nat.pred (y0 y1 y2))).
Definition term80 := exists y0 : type1606, (forall y1 : nat, (y0 (NUMERAL 0) y1) = y1) /\ (forall y1 : nat, forall y2 : nat, (y0 (S y2) y1) = (Nat.pred (y0 y2 y1))).
Definition term66 := fun y0 : nat -> nat => fun y1 : nat => fun y2 : nat => Nat.pred (y0 y2).
Definition term74 (x0 : type1606) := forall y0 : nat, (x0 (S y0)) = ((fun y1 : nat -> nat => fun y2 : nat => fun y3 : nat => Nat.pred (y1 y3)) (x0 y0) y0).
Definition term53 (x0 : nat) := (fun y0 : nat => y0) x0.
Definition term43 (x0 : type1606) (x1 : nat) := forall y0 : nat, (x0 x1 (S y0)) = (Nat.pred (x0 x1 y0)).
Definition term39 (x0 : type1606) (x1 : nat) (x2 : nat) := @eq nat ((fun y0 : nat => x0 y0 x1) x2).
Definition term88 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term113 := exists y0 : type1602, forall y1 : nat, (forall y2 : nat, (y0 y1 y2 (NUMERAL 0)) = y2) /\ (forall y2 : nat, forall y3 : nat, (y0 y1 y2 (S y3)) = (Nat.pred (y0 y1 y2 y3))).
Definition term93 := exists y0 : type1602, forall y1 : nat, (fun y2 : nat => fun y3 : type1606 => (forall y4 : nat, (y3 y4 (NUMERAL 0)) = y4) /\ (forall y4 : nat, forall y5 : nat, (y3 y4 (S y5)) = (Nat.pred (y3 y4 y5)))) y1 (y0 y1).
Definition term91 (x0 : type1581) := exists y0 : type1602, forall y1 : nat, x0 y1 (y0 y1).
Definition term98 (x0 : nat) := fun y0 : type1606 => (fun y1 : nat => fun y2 : type1606 => (forall y3 : nat, (y2 y3 (NUMERAL 0)) = y3) /\ (forall y3 : nat, forall y4 : nat, (y2 y3 (S y4)) = (Nat.pred (y2 y3 y4)))) x0 y0.
Definition term38 (x0 : type1606) (x1 : nat) (x2 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) x2).
Definition term76 (x0 : type1606) := ((x0 (NUMERAL 0)) = (fun y0 : nat => y0)) /\ (forall y0 : nat, (x0 (S y0)) = ((fun y1 : nat -> nat => fun y2 : nat => fun y3 : nat => Nat.pred (y1 y3)) (x0 y0) y0)).
Definition term115 := fun y0 : type957 => y0 (@ε (nat -> nat -> nat -> nat) y0).
Definition term106 (x0 : type1602) (x1 : nat) := (forall y0 : nat, (x0 x1 y0 (NUMERAL 0)) = y0) /\ (forall y0 : nat, forall y1 : nat, (x0 x1 y0 (S y1)) = (Nat.pred (x0 x1 y0 y1))).
Definition term50 (x0 : type1606) := (forall y0 : nat, (x0 (NUMERAL 0) y0) = y0) /\ (forall y0 : nat, forall y1 : nat, (x0 (S y1) y0) = (Nat.pred (x0 y1 y0))).
Definition term49 (x0 : type1606) := (forall y0 : nat, (x0 y0 (NUMERAL 0)) = y0) /\ (forall y0 : nat, forall y1 : nat, (x0 y0 (S y1)) = (Nat.pred (x0 y0 y1))).
Definition term8 (x0 : type1606) (x1 : nat) := fun y0 : nat => x0 y0 x1.
Definition term72 (x0 : type1606) := fun y0 : nat => (x0 (S y0)) = ((fun y1 : nat -> nat => fun y2 : nat => fun y3 : nat => Nat.pred (y1 y3)) (x0 y0) y0).
Definition term20 (x0 : type1606) (x1 : nat) := x0 (NUMERAL 0) x1.
Definition term34 (x0 : type1606) (x1 : nat) (x2 : nat) := x0 (S x1) x2.
Definition term60 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : type1423 a0, exists y2 : nat -> a0, ((y2 (NUMERAL 0)) = y0) /\ (forall y3 : nat, (y2 (S y3)) = (y1 (y2 y3) y3))) x0.
Definition term109 (x0 : type1602) := forall y0 : nat, (fun y1 : nat => fun y2 : type1606 => (forall y3 : nat, (y2 y3 (NUMERAL 0)) = y3) /\ (forall y3 : nat, forall y4 : nat, (y2 y3 (S y4)) = (Nat.pred (y2 y3 y4)))) y0 (x0 y0).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => ((fun y1 : a0 => x0 y1) y0) = (x0 y0)) x1.
Definition term94 := fun y0 : nat => fun y1 : type1606 => (forall y2 : nat, (y1 y2 (NUMERAL 0)) = y2) /\ (forall y2 : nat, forall y3 : nat, (y1 y2 (S y3)) = (Nat.pred (y1 y2 y3))).
Definition term25 (x0 : type1606) := forall y0 : nat, (x0 y0 (NUMERAL 0)) = y0.
Definition term105 (x0 : type1602) (x1 : nat) := (fun y0 : type1606 => (forall y1 : nat, (y0 y1 (NUMERAL 0)) = y1) /\ (forall y1 : nat, forall y2 : nat, (y0 y1 (S y2)) = (Nat.pred (y0 y1 y2)))) (x0 x1).
Definition term30 (x0 : type1606) (x1 : nat) (x2 : nat) := (fun y0 : nat => x0 y0 x1) (S x2).
Definition term18 (x0 : type1606) (x1 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) (NUMERAL 0)).
Definition term112 := fun y0 : type1602 => forall y1 : nat, (forall y2 : nat, (y0 y1 y2 (NUMERAL 0)) = y2) /\ (forall y2 : nat, forall y3 : nat, (y0 y1 y2 (S y3)) = (Nat.pred (y0 y1 y2 y3))).
Definition term111 := fun y0 : type1602 => forall y1 : nat, (fun y2 : nat => fun y3 : type1606 => (forall y4 : nat, (y3 y4 (NUMERAL 0)) = y4) /\ (forall y4 : nat, forall y5 : nat, (y3 y4 (S y5)) = (Nat.pred (y3 y4 y5)))) y1 (y0 y1).
Definition term103 := @eq Prop (forall y0 : nat, exists y1 : type1606, (forall y2 : nat, (y1 y2 (NUMERAL 0)) = y2) /\ (forall y2 : nat, forall y3 : nat, (y1 y2 (S y3)) = (Nat.pred (y1 y2 y3)))).
Definition term102 := @eq Prop (forall y0 : nat, exists y1 : type1606, (fun y2 : nat => fun y3 : type1606 => (forall y4 : nat, (y3 y4 (NUMERAL 0)) = y4) /\ (forall y4 : nat, forall y5 : nat, (y3 y4 (S y5)) = (Nat.pred (y3 y4 y5)))) y0 y1).
Definition term33 (x0 : type1606) (x1 : nat) (x2 : nat) := @eq nat ((fun y0 : nat => x0 y0 x1) (S x2)).
Definition term19 (x0 : type1606) (x1 : nat) := @eq nat ((fun y0 : nat => x0 y0 x1) (NUMERAL 0)).
Definition term5 (x0 : type1606) (x1 : nat) := (fun y0 : nat => fun y1 : nat => x0 y1 y0) x1.
Definition term79 := exists y0 : type1606, ((y0 (NUMERAL 0)) = (fun y1 : nat => y1)) /\ (forall y1 : nat, (y0 (S y1)) = (fun y2 : nat => Nat.pred (y0 y1 y2))).
Definition term65 := exists y0 : type1606, ((y0 (NUMERAL 0)) = (fun y1 : nat => y1)) /\ (forall y1 : nat, (y0 (S y1)) = ((fun y2 : nat -> nat => fun y3 : nat => fun y4 : nat => Nat.pred (y2 y4)) (y0 y1) y1)).
Definition term114 (a0 : Type') := fun y0 : a0 -> Prop => y0 (@ε a0 y0).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term58 (x0 : type1606) (x1 : nat) (x2 : nat) := (fun y0 : nat => Nat.pred (x0 x1 y0)) x2.
Definition term28 (x0 : type1606) := and (forall y0 : nat, (x0 (NUMERAL 0) y0) = y0).
Definition term27 (x0 : type1606) := and (forall y0 : nat, (x0 y0 (NUMERAL 0)) = y0).
Definition term55 (x0 : type1606) (x1 : nat) := (fun y0 : nat => (x0 (S y0)) = (fun y1 : nat => Nat.pred (x0 y0 y1))) x1.
Definition term52 := fun y0 : nat => y0.
Definition term35 (x0 : type1606) (x1 : nat) (x2 : nat) := @eq nat (x0 x1 (S x2)).
Definition term116 := (fun y0 : type957 => y0 (@ε (nat -> nat -> nat -> nat) y0)) (fun y0 : type1602 => forall y1 : nat, (forall y2 : nat, (y0 y1 y2 (NUMERAL 0)) = y2) /\ (forall y2 : nat, forall y3 : nat, (y0 y1 y2 (S y3)) = (Nat.pred (y0 y1 y2 y3)))).
Definition term48 (x0 : type1606) := forall y0 : nat, forall y1 : nat, (x0 (S y1) y0) = (Nat.pred (x0 y1 y0)).
Definition term47 (x0 : type1606) := forall y0 : nat, forall y1 : nat, (x0 y0 (S y1)) = (Nat.pred (x0 y0 y1)).
Definition term41 (x0 : type1606) (x1 : nat) := fun y0 : nat => (x0 x1 (S y0)) = (Nat.pred (x0 x1 y0)).
Definition term14 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term6 (x0 : type1606) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term32 (x0 : type1606) (x1 : nat) (x2 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) (S x2)).
Definition term99 (x0 : nat) := exists y0 : type1606, (fun y1 : nat => fun y2 : type1606 => (forall y3 : nat, (y2 y3 (NUMERAL 0)) = y3) /\ (forall y3 : nat, forall y4 : nat, (y2 y3 (S y4)) = (Nat.pred (y2 y3 y4)))) x0 y0.
Definition term83 := fun y0 : type1606 => (forall y1 : nat, (y0 y1 (NUMERAL 0)) = y1) /\ (forall y1 : nat, forall y2 : nat, (y0 y1 (S y2)) = (Nat.pred (y0 y1 y2))).
Definition term81 := fun y0 : type1606 => (forall y1 : nat, (y0 (NUMERAL 0) y1) = y1) /\ (forall y1 : nat, forall y2 : nat, (y0 (S y2) y1) = (Nat.pred (y0 y2 y1))).
Definition term68 (x0 : type1606) (x1 : nat) := fun y0 : nat => fun y1 : nat => Nat.pred (x0 x1 y1).
Definition term101 := fun y0 : nat => exists y1 : type1606, (forall y2 : nat, (y1 y2 (NUMERAL 0)) = y2) /\ (forall y2 : nat, forall y3 : nat, (y1 y2 (S y3)) = (Nat.pred (y1 y2 y3))).
Definition term100 := fun y0 : nat => exists y1 : type1606, (fun y2 : nat => fun y3 : type1606 => (forall y4 : nat, (y3 y4 (NUMERAL 0)) = y4) /\ (forall y4 : nat, forall y5 : nat, (y3 y4 (S y5)) = (Nat.pred (y3 y4 y5)))) y0 y1.
Definition term97 (x0 : type1606) := (fun y0 : type1606 => (forall y1 : nat, (y0 y1 (NUMERAL 0)) = y1) /\ (forall y1 : nat, forall y2 : nat, (y0 y1 (S y2)) = (Nat.pred (y0 y1 y2)))) x0.
Definition term26 (x0 : type1606) := forall y0 : nat, (x0 (NUMERAL 0) y0) = y0.
Definition term75 (x0 : type1606) := and ((x0 (NUMERAL 0)) = (fun y0 : nat => y0)).
Definition term7 (x0 : type1606) (x1 : nat) := (fun y0 : nat => (fun y1 : nat => fun y2 : nat => x0 y2 y1) y0) x1.
Definition term13 (x0 : type1606) (x1 : nat) := (fun y0 : nat => x0 y0 x1) (NUMERAL 0).
Definition term95 (x0 : nat) := (fun y0 : nat => fun y1 : type1606 => (forall y2 : nat, (y1 y2 (NUMERAL 0)) = y2) /\ (forall y2 : nat, forall y3 : nat, (y1 y2 (S y3)) = (Nat.pred (y1 y2 y3)))) x0.
Definition term22 (x0 : type1606) (x1 : nat) := @eq nat (x0 (NUMERAL 0) x1).
Definition term51 (x0 : type1606) := x0 (NUMERAL 0).
Definition term12 (x0 : type1606) (x1 : nat) := x0 x1 (NUMERAL 0).
Definition term71 (x0 : type1606) (x1 : nat) := @eq (nat -> nat) (x0 (S x1)).
Definition term84 (x0 : type1606) (x1 : type1606) := (x0 = (fun y0 : nat => fun y1 : nat => x1 y1 y0)) -> exists y0 : type1606, (forall y1 : nat, (y0 y1 (NUMERAL 0)) = y1) /\ (forall y1 : nat, forall y2 : nat, (y0 y1 (S y2)) = (Nat.pred (y0 y1 y2))).
Definition term104 (x0 : type1602) (x1 : nat) := (fun y0 : nat => fun y1 : type1606 => (forall y2 : nat, (y1 y2 (NUMERAL 0)) = y2) /\ (forall y2 : nat, forall y3 : nat, (y1 y2 (S y3)) = (Nat.pred (y1 y2 y3)))) x1 (x0 x1).
Definition term10 (x0 : type1606) (x1 : nat) := @eq (nat -> nat) ((fun y0 : nat => (fun y1 : nat => fun y2 : nat => x0 y2 y1) y0) x1).
Definition term44 (x0 : type1606) (x1 : nat) := forall y0 : nat, (x0 (S y0) x1) = (Nat.pred (x0 y0 x1)).
Definition term73 (x0 : type1606) := fun y0 : nat => (x0 (S y0)) = (fun y1 : nat => Nat.pred (x0 y0 y1)).
Definition term56 (x0 : type1606) (x1 : nat) := x0 (S x1).
Definition term46 (x0 : type1606) := fun y0 : nat => forall y1 : nat, (x0 (S y1) y0) = (Nat.pred (x0 y1 y0)).
Definition term45 (x0 : type1606) := fun y0 : nat => forall y1 : nat, (x0 y0 (S y1)) = (Nat.pred (x0 y0 y1)).
Definition term61 (a0 : Type') (x0 : a0) := forall y0 : type1423 a0, exists y1 : nat -> a0, ((y1 (NUMERAL 0)) = x0) /\ (forall y2 : nat, (y1 (S y2)) = (y0 (y1 y2) y2)).
Definition term87 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => (forall y1 : a0, exists y2 : a1, y0 y1 y2) = (exists y1 : a0 -> a1, forall y2 : a0, y0 y2 (y1 y2))) x0.
Definition term110 (x0 : type1602) := forall y0 : nat, (forall y1 : nat, (x0 y0 y1 (NUMERAL 0)) = y1) /\ (forall y1 : nat, forall y2 : nat, (x0 y0 y1 (S y2)) = (Nat.pred (x0 y0 y1 y2))).
Definition term78 := fun y0 : type1606 => ((y0 (NUMERAL 0)) = (fun y1 : nat => y1)) /\ (forall y1 : nat, (y0 (S y1)) = (fun y2 : nat => Nat.pred (y0 y1 y2))).
Definition term77 := fun y0 : type1606 => ((y0 (NUMERAL 0)) = (fun y1 : nat => y1)) /\ (forall y1 : nat, (y0 (S y1)) = ((fun y2 : nat -> nat => fun y3 : nat => fun y4 : nat => Nat.pred (y2 y4)) (y0 y1) y1)).
Definition term24 (x0 : type1606) := fun y0 : nat => (x0 (NUMERAL 0) y0) = y0.
Definition term23 (x0 : type1606) := fun y0 : nat => (x0 y0 (NUMERAL 0)) = y0.
Definition term31 (x0 : type1606) (x1 : nat) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) (S x2).
Definition term89 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term64 (x0 : nat -> nat) (x1 : type1000) := exists y0 : type1606, ((y0 (NUMERAL 0)) = x0) /\ (forall y1 : nat, (y0 (S y1)) = (x1 (y0 y1) y1)).
Definition term63 (a0 : Type') (x0 : a0) (x1 : type1423 a0) := exists y0 : nat -> a0, ((y0 (NUMERAL 0)) = x0) /\ (forall y1 : nat, (y0 (S y1)) = (x1 (y0 y1) y1)).
Definition term37 (x0 : type1606) (x1 : nat) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) x2.
Definition term36 (x0 : type1606) (x1 : nat) (x2 : nat) := @eq nat (x0 (S x1) x2).
Definition term59 (x0 : type1606) := ((x0 (NUMERAL 0)) = (fun y0 : nat => y0)) /\ (forall y0 : nat, (x0 (S y0)) = (fun y1 : nat => Nat.pred (x0 y0 y1))).
Definition term54 (x0 : type1606) := forall y0 : nat, (x0 (S y0)) = (fun y1 : nat => Nat.pred (x0 y0 y1)).
Definition term85 (x0 : type1606) := ((fun y0 : nat => fun y1 : nat => x0 y1 y0) = (fun y0 : nat => fun y1 : nat => x0 y1 y0)) -> exists y0 : type1606, (forall y1 : nat, (y0 y1 (NUMERAL 0)) = y1) /\ (forall y1 : nat, forall y2 : nat, (y0 y1 (S y2)) = (Nat.pred (y0 y1 y2))).
Definition term21 (x0 : type1606) (x1 : nat) := @eq nat (x0 x1 (NUMERAL 0)).
Definition term96 (x0 : nat) (x1 : type1606) := (fun y0 : nat => fun y1 : type1606 => (forall y2 : nat, (y1 y2 (NUMERAL 0)) = y2) /\ (forall y2 : nat, forall y3 : nat, (y1 y2 (S y3)) = (Nat.pred (y1 y2 y3)))) x0 x1.
Definition term16 (x0 : type1606) (x1 : nat) (x2 : nat) := (fun y0 : nat => x0 y0 x1) x2.
