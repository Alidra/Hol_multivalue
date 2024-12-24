Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term61 (x0 : type1602) := fun y0 : nat => (fun y1 : nat => fun y2 : type1606 => (forall y3 : nat, (y2 (NUMERAL 0) y3) = (NUMERAL 0)) /\ (forall y3 : nat, forall y4 : nat, (y2 (S y3) y4) = (Nat.add (y2 y3 y4) y4))) y0 (x0 y0).
Definition term12 (x0 : type1606) (x1 : nat) (x2 : nat) := Nat.add (x0 x1 x2) x2.
Definition term7 (x0 : type1606) (x1 : nat) := (fun y0 : nat => (x0 (S y0)) = (fun y1 : nat => Nat.add (x0 y0 y1) y1)) x1.
Definition term25 (x0 : type1606) (x1 : nat) := (fun y0 : nat -> nat => fun y1 : nat => fun y2 : nat => Nat.add (y0 y2) y2) (x0 x1).
Definition term5 (x0 : type1606) := forall y0 : nat, (x0 (NUMERAL 0) y0) = (NUMERAL 0).
Definition term28 (x0 : type1606) (x1 : nat) := (fun y0 : nat => fun y1 : nat => Nat.add (x0 x1 y1) y1) x1.
Definition term46 := forall y0 : nat, exists y1 : type1606, (fun y2 : nat => fun y3 : type1606 => (forall y4 : nat, (y3 (NUMERAL 0) y4) = (NUMERAL 0)) /\ (forall y4 : nat, forall y5 : nat, (y3 (S y4) y5) = (Nat.add (y3 y4 y5) y5))) y0 y1.
Definition term44 (x0 : type1581) := forall y0 : nat, exists y1 : type1606, x0 y0 y1.
Definition term40 := forall y0 : nat, exists y1 : type1606, (forall y2 : nat, (y1 (NUMERAL 0) y2) = (NUMERAL 0)) /\ (forall y2 : nat, forall y3 : nat, (y1 (S y2) y3) = (Nat.add (y1 y2 y3) y3)).
Definition term20 (a0 : Type') (x0 : a0) (x1 : type1423 a0) := (fun y0 : type1423 a0 => exists y1 : nat -> a0, ((y1 (NUMERAL 0)) = x0) /\ (forall y2 : nat, (y1 (S y2)) = (y0 (y1 y2) y2))) x1.
Definition term27 (x0 : type1606) (x1 : nat) := (fun y0 : nat -> nat => fun y1 : nat => fun y2 : nat => Nat.add (y0 y2) y2) (x0 x1) x1.
Definition term62 (x0 : type1602) := fun y0 : nat => (forall y1 : nat, (x0 y0 (NUMERAL 0) y1) = (NUMERAL 0)) /\ (forall y1 : nat, forall y2 : nat, (x0 y0 (S y1) y2) = (Nat.add (x0 y0 y1 y2) y2)).
Definition term71 := (fun y0 : type1602 => forall y1 : nat, (forall y2 : nat, (y0 y1 (NUMERAL 0) y2) = (NUMERAL 0)) /\ (forall y2 : nat, forall y3 : nat, (y0 y1 (S y2) y3) = (Nat.add (y0 y1 y2 y3) y3))) (@ε (nat -> nat -> nat -> nat) (fun y0 : type1602 => forall y1 : nat, (forall y2 : nat, (y0 y1 (NUMERAL 0) y2) = (NUMERAL 0)) /\ (forall y2 : nat, forall y3 : nat, (y0 y1 (S y2) y3) = (Nat.add (y0 y1 y2 y3) y3)))).
Definition term38 := exists y0 : type1606, (forall y1 : nat, (y0 (NUMERAL 0) y1) = (NUMERAL 0)) /\ (forall y1 : nat, forall y2 : nat, (y0 (S y1) y2) = (Nat.add (y0 y1 y2) y2)).
Definition term32 (x0 : type1606) := forall y0 : nat, (x0 (S y0)) = ((fun y1 : nat -> nat => fun y2 : nat => fun y3 : nat => Nat.add (y1 y3) y3) (x0 y0) y0).
Definition term6 (x0 : type1606) := forall y0 : nat, (x0 (S y0)) = (fun y1 : nat => Nat.add (x0 y0 y1) y1).
Definition term42 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term3 (x0 : nat) := (fun y0 : nat => NUMERAL 0) x0.
Definition term67 := exists y0 : type1602, forall y1 : nat, (forall y2 : nat, (y0 y1 (NUMERAL 0) y2) = (NUMERAL 0)) /\ (forall y2 : nat, forall y3 : nat, (y0 y1 (S y2) y3) = (Nat.add (y0 y1 y2 y3) y3)).
Definition term47 := exists y0 : type1602, forall y1 : nat, (fun y2 : nat => fun y3 : type1606 => (forall y4 : nat, (y3 (NUMERAL 0) y4) = (NUMERAL 0)) /\ (forall y4 : nat, forall y5 : nat, (y3 (S y4) y5) = (Nat.add (y3 y4 y5) y5))) y1 (y0 y1).
Definition term45 (x0 : type1581) := exists y0 : type1602, forall y1 : nat, x0 y1 (y0 y1).
Definition term52 (x0 : nat) := fun y0 : type1606 => (fun y1 : nat => fun y2 : type1606 => (forall y3 : nat, (y2 (NUMERAL 0) y3) = (NUMERAL 0)) /\ (forall y3 : nat, forall y4 : nat, (y2 (S y3) y4) = (Nat.add (y2 y3 y4) y4))) x0 y0.
Definition term69 := fun y0 : type957 => y0 (@ε (nat -> nat -> nat -> nat) y0).
Definition term30 (x0 : type1606) := fun y0 : nat => (x0 (S y0)) = ((fun y1 : nat -> nat => fun y2 : nat => fun y3 : nat => Nat.add (y1 y3) y3) (x0 y0) y0).
Definition term2 (x0 : type1606) (x1 : nat) := x0 (NUMERAL 0) x1.
Definition term10 (x0 : type1606) (x1 : nat) (x2 : nat) := x0 (S x1) x2.
Definition term18 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : type1423 a0, exists y2 : nat -> a0, ((y2 (NUMERAL 0)) = y0) /\ (forall y3 : nat, (y2 (S y3)) = (y1 (y2 y3) y3))) x0.
Definition term33 (x0 : type1606) := and ((x0 (NUMERAL 0)) = (fun y0 : nat => NUMERAL 0)).
Definition term63 (x0 : type1602) := forall y0 : nat, (fun y1 : nat => fun y2 : type1606 => (forall y3 : nat, (y2 (NUMERAL 0) y3) = (NUMERAL 0)) /\ (forall y3 : nat, forall y4 : nat, (y2 (S y3) y4) = (Nat.add (y2 y3 y4) y4))) y0 (x0 y0).
Definition term48 := fun y0 : nat => fun y1 : type1606 => (forall y2 : nat, (y1 (NUMERAL 0) y2) = (NUMERAL 0)) /\ (forall y2 : nat, forall y3 : nat, (y1 (S y2) y3) = (Nat.add (y1 y2 y3) y3)).
Definition term59 (x0 : type1602) (x1 : nat) := (fun y0 : type1606 => (forall y1 : nat, (y0 (NUMERAL 0) y1) = (NUMERAL 0)) /\ (forall y1 : nat, forall y2 : nat, (y0 (S y1) y2) = (Nat.add (y0 y1 y2) y2))) (x0 x1).
Definition term1 := fun y0 : nat => NUMERAL 0.
Definition term66 := fun y0 : type1602 => forall y1 : nat, (forall y2 : nat, (y0 y1 (NUMERAL 0) y2) = (NUMERAL 0)) /\ (forall y2 : nat, forall y3 : nat, (y0 y1 (S y2) y3) = (Nat.add (y0 y1 y2 y3) y3)).
Definition term65 := fun y0 : type1602 => forall y1 : nat, (fun y2 : nat => fun y3 : type1606 => (forall y4 : nat, (y3 (NUMERAL 0) y4) = (NUMERAL 0)) /\ (forall y4 : nat, forall y5 : nat, (y3 (S y4) y5) = (Nat.add (y3 y4 y5) y5))) y1 (y0 y1).
Definition term57 := @eq Prop (forall y0 : nat, exists y1 : type1606, (forall y2 : nat, (y1 (NUMERAL 0) y2) = (NUMERAL 0)) /\ (forall y2 : nat, forall y3 : nat, (y1 (S y2) y3) = (Nat.add (y1 y2 y3) y3))).
Definition term56 := @eq Prop (forall y0 : nat, exists y1 : type1606, (fun y2 : nat => fun y3 : type1606 => (forall y4 : nat, (y3 (NUMERAL 0) y4) = (NUMERAL 0)) /\ (forall y4 : nat, forall y5 : nat, (y3 (S y4) y5) = (Nat.add (y3 y4 y5) y5))) y0 y1).
Definition term37 := exists y0 : type1606, ((y0 (NUMERAL 0)) = (fun y1 : nat => NUMERAL 0)) /\ (forall y1 : nat, (y0 (S y1)) = (fun y2 : nat => Nat.add (y0 y1 y2) y2)).
Definition term23 := exists y0 : type1606, ((y0 (NUMERAL 0)) = (fun y1 : nat => NUMERAL 0)) /\ (forall y1 : nat, (y0 (S y1)) = ((fun y2 : nat -> nat => fun y3 : nat => fun y4 : nat => Nat.add (y2 y4) y4) (y0 y1) y1)).
Definition term68 (a0 : Type') := fun y0 : a0 -> Prop => y0 (@ε a0 y0).
Definition term70 := (fun y0 : type957 => y0 (@ε (nat -> nat -> nat -> nat) y0)) (fun y0 : type1602 => forall y1 : nat, (forall y2 : nat, (y0 y1 (NUMERAL 0) y2) = (NUMERAL 0)) /\ (forall y2 : nat, forall y3 : nat, (y0 y1 (S y2) y3) = (Nat.add (y0 y1 y2 y3) y3))).
Definition term15 (x0 : type1606) := forall y0 : nat, forall y1 : nat, (x0 (S y0) y1) = (Nat.add (x0 y0 y1) y1).
Definition term31 (x0 : type1606) := fun y0 : nat => (x0 (S y0)) = (fun y1 : nat => Nat.add (x0 y0 y1) y1).
Definition term53 (x0 : nat) := exists y0 : type1606, (fun y1 : nat => fun y2 : type1606 => (forall y3 : nat, (y2 (NUMERAL 0) y3) = (NUMERAL 0)) /\ (forall y3 : nat, forall y4 : nat, (y2 (S y3) y4) = (Nat.add (y2 y3 y4) y4))) x0 y0.
Definition term39 := fun y0 : type1606 => (forall y1 : nat, (y0 (NUMERAL 0) y1) = (NUMERAL 0)) /\ (forall y1 : nat, forall y2 : nat, (y0 (S y1) y2) = (Nat.add (y0 y1 y2) y2)).
Definition term55 := fun y0 : nat => exists y1 : type1606, (forall y2 : nat, (y1 (NUMERAL 0) y2) = (NUMERAL 0)) /\ (forall y2 : nat, forall y3 : nat, (y1 (S y2) y3) = (Nat.add (y1 y2 y3) y3)).
Definition term54 := fun y0 : nat => exists y1 : type1606, (fun y2 : nat => fun y3 : type1606 => (forall y4 : nat, (y3 (NUMERAL 0) y4) = (NUMERAL 0)) /\ (forall y4 : nat, forall y5 : nat, (y3 (S y4) y5) = (Nat.add (y3 y4 y5) y5))) y0 y1.
Definition term51 (x0 : type1606) := (fun y0 : type1606 => (forall y1 : nat, (y0 (NUMERAL 0) y1) = (NUMERAL 0)) /\ (forall y1 : nat, forall y2 : nat, (y0 (S y1) y2) = (Nat.add (y0 y1 y2) y2))) x0.
Definition term16 (x0 : type1606) := ((x0 (NUMERAL 0)) = (fun y0 : nat => NUMERAL 0)) /\ (forall y0 : nat, (x0 (S y0)) = (fun y1 : nat => Nat.add (x0 y0 y1) y1)).
Definition term14 (x0 : type1606) (x1 : nat) := forall y0 : nat, (x0 (S x1) y0) = (Nat.add (x0 x1 y0) y0).
Definition term49 (x0 : nat) := (fun y0 : nat => fun y1 : type1606 => (forall y2 : nat, (y1 (NUMERAL 0) y2) = (NUMERAL 0)) /\ (forall y2 : nat, forall y3 : nat, (y1 (S y2) y3) = (Nat.add (y1 y2 y3) y3))) x0.
Definition term4 (x0 : type1606) (x1 : nat) := @eq nat (x0 (NUMERAL 0) x1).
Definition term60 (x0 : type1602) (x1 : nat) := (forall y0 : nat, (x0 x1 (NUMERAL 0) y0) = (NUMERAL 0)) /\ (forall y0 : nat, forall y1 : nat, (x0 x1 (S y0) y1) = (Nat.add (x0 x1 y0 y1) y1)).
Definition term17 (x0 : type1606) := (forall y0 : nat, (x0 (NUMERAL 0) y0) = (NUMERAL 0)) /\ (forall y0 : nat, forall y1 : nat, (x0 (S y0) y1) = (Nat.add (x0 y0 y1) y1)).
Definition term26 (x0 : type1606) (x1 : nat) := fun y0 : nat => fun y1 : nat => Nat.add (x0 x1 y1) y1.
Definition term34 (x0 : type1606) := ((x0 (NUMERAL 0)) = (fun y0 : nat => NUMERAL 0)) /\ (forall y0 : nat, (x0 (S y0)) = ((fun y1 : nat -> nat => fun y2 : nat => fun y3 : nat => Nat.add (y1 y3) y3) (x0 y0) y0)).
Definition term0 (x0 : type1606) := x0 (NUMERAL 0).
Definition term9 (x0 : type1606) (x1 : nat) := fun y0 : nat => Nat.add (x0 x1 y0) y0.
Definition term29 (x0 : type1606) (x1 : nat) := @eq (nat -> nat) (x0 (S x1)).
Definition term36 := fun y0 : type1606 => ((y0 (NUMERAL 0)) = (fun y1 : nat => NUMERAL 0)) /\ (forall y1 : nat, (y0 (S y1)) = (fun y2 : nat => Nat.add (y0 y1 y2) y2)).
Definition term35 := fun y0 : type1606 => ((y0 (NUMERAL 0)) = (fun y1 : nat => NUMERAL 0)) /\ (forall y1 : nat, (y0 (S y1)) = ((fun y2 : nat -> nat => fun y3 : nat => fun y4 : nat => Nat.add (y2 y4) y4) (y0 y1) y1)).
Definition term58 (x0 : type1602) (x1 : nat) := (fun y0 : nat => fun y1 : type1606 => (forall y2 : nat, (y1 (NUMERAL 0) y2) = (NUMERAL 0)) /\ (forall y2 : nat, forall y3 : nat, (y1 (S y2) y3) = (Nat.add (y1 y2 y3) y3))) x1 (x0 x1).
Definition term8 (x0 : type1606) (x1 : nat) := x0 (S x1).
Definition term19 (a0 : Type') (x0 : a0) := forall y0 : type1423 a0, exists y1 : nat -> a0, ((y1 (NUMERAL 0)) = x0) /\ (forall y2 : nat, (y1 (S y2)) = (y0 (y1 y2) y2)).
Definition term41 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => (forall y1 : a0, exists y2 : a1, y0 y1 y2) = (exists y1 : a0 -> a1, forall y2 : a0, y0 y2 (y1 y2))) x0.
Definition term64 (x0 : type1602) := forall y0 : nat, (forall y1 : nat, (x0 y0 (NUMERAL 0) y1) = (NUMERAL 0)) /\ (forall y1 : nat, forall y2 : nat, (x0 y0 (S y1) y2) = (Nat.add (x0 y0 y1 y2) y2)).
Definition term24 := fun y0 : nat -> nat => fun y1 : nat => fun y2 : nat => Nat.add (y0 y2) y2.
Definition term43 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term22 (x0 : nat -> nat) (x1 : type1000) := exists y0 : type1606, ((y0 (NUMERAL 0)) = x0) /\ (forall y1 : nat, (y0 (S y1)) = (x1 (y0 y1) y1)).
Definition term21 (a0 : Type') (x0 : a0) (x1 : type1423 a0) := exists y0 : nat -> a0, ((y0 (NUMERAL 0)) = x0) /\ (forall y1 : nat, (y0 (S y1)) = (x1 (y0 y1) y1)).
Definition term13 (x0 : type1606) (x1 : nat) (x2 : nat) := @eq nat (x0 (S x1) x2).
Definition term11 (x0 : type1606) (x1 : nat) (x2 : nat) := (fun y0 : nat => Nat.add (x0 x1 y0) y0) x2.
Definition term50 (x0 : nat) (x1 : type1606) := (fun y0 : nat => fun y1 : type1606 => (forall y2 : nat, (y1 (NUMERAL 0) y2) = (NUMERAL 0)) /\ (forall y2 : nat, forall y3 : nat, (y1 (S y2) y3) = (Nat.add (y1 y2 y3) y3))) x0 x1.
