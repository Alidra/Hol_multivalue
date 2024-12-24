Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0, ((fun y2 : a0 => y0 y2) y1) = (y0 y1)) x0.
Definition term114 := fun y0 : type1306 => forall y1 : type1674, (forall y2 : nat, (y0 y1 y2 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y2 : nat, forall y3 : nat, (y0 y1 y2 (S y3)) = (Nat.mul y2 (y0 y1 y2 y3))).
Definition term105 := @eq Prop (forall y0 : type1674, exists y1 : type1606, (forall y2 : nat, (y1 y2 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y2 : nat, forall y3 : nat, (y1 y2 (S y3)) = (Nat.mul y2 (y1 y2 y3)))).
Definition term104 := @eq Prop (forall y0 : type1674, exists y1 : type1606, (fun y2 : type1674 => fun y3 : type1606 => (forall y4 : nat, (y3 y4 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y4 : nat, forall y5 : nat, (y3 y4 (S y5)) = (Nat.mul y4 (y3 y4 y5)))) y0 y1).
Definition term30 (x0 : type1606) (x1 : nat) (x2 : nat) := x0 x1 (S x2).
Definition term113 := fun y0 : type1306 => forall y1 : type1674, (fun y2 : type1674 => fun y3 : type1606 => (forall y4 : nat, (y3 y4 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y4 : nat, forall y5 : nat, (y3 y4 (S y5)) = (Nat.mul y4 (y3 y4 y5)))) y1 (y0 y1).
Definition term54 := fun y0 : nat => NUMERAL (BIT1 0).
Definition term100 (x0 : type1674) := fun y0 : type1606 => (fun y1 : type1674 => fun y2 : type1606 => (forall y3 : nat, (y2 y3 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y3 : nat, forall y4 : nat, (y2 y3 (S y4)) = (Nat.mul y3 (y2 y3 y4)))) x0 y0.
Definition term69 (x0 : type1606) (x1 : nat) := (fun y0 : nat -> nat => fun y1 : nat => fun y2 : nat => Nat.mul y2 (y0 y2)) (x0 x1).
Definition term4 (x0 : type1606) := fun y0 : nat => fun y1 : nat => x0 y1 y0.
Definition term25 (x0 : type1606) := fun y0 : nat => (x0 (NUMERAL 0) y0) = (NUMERAL (BIT1 0)).
Definition term56 (x0 : type1606) := forall y0 : nat, (x0 (S y0)) = (fun y1 : nat => Nat.mul y1 (x0 y0 y1)).
Definition term98 (x0 : type1674) (x1 : type1606) := (fun y0 : type1674 => fun y1 : type1606 => (forall y2 : nat, (y1 y2 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y2 : nat, forall y3 : nat, (y1 y2 (S y3)) = (Nat.mul y2 (y1 y2 y3)))) x0 x1.
Definition term11 (x0 : type1606) (x1 : nat) := @eq (nat -> nat) ((fun y0 : nat => fun y1 : nat => x0 y1 y0) x1).
Definition term96 := fun y0 : type1674 => fun y1 : type1606 => (forall y2 : nat, (y1 y2 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y2 : nat, forall y3 : nat, (y1 y2 (S y3)) = (Nat.mul y2 (y1 y2 y3))).
Definition term17 (x0 : type1606) (x1 : nat) := fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0, ((fun y1 : a0 => x0 y1) y0) = (x0 y0).
Definition term55 (x0 : nat) := (fun y0 : nat => NUMERAL (BIT1 0)) x0.
Definition term45 (x0 : type1606) (x1 : nat) := forall y0 : nat, (x0 x1 (S y0)) = (Nat.mul x1 (x0 x1 y0)).
Definition term9 (x0 : type1606) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => x0 y2 y1) y0.
Definition term64 (a0 : Type') (x0 : a0) (x1 : type1423 a0) := (fun y0 : type1423 a0 => exists y1 : nat -> a0, ((y1 (NUMERAL 0)) = x0) /\ (forall y2 : nat, (y1 (S y2)) = (y0 (y1 y2) y2))) x1.
Definition term71 (x0 : type1606) (x1 : nat) := (fun y0 : nat -> nat => fun y1 : nat => fun y2 : nat => Nat.mul y2 (y0 y2)) (x0 x1) x1.
Definition term24 (x0 : type1606) := fun y0 : nat => (x0 y0 (NUMERAL 0)) = (NUMERAL (BIT1 0)).
Definition term15 (x0 : type1606) (x1 : nat) := (fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) (NUMERAL 0).
Definition term119 := (fun y0 : type1306 => forall y1 : type1674, (forall y2 : nat, (y0 y1 y2 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y2 : nat, forall y3 : nat, (y0 y1 y2 (S y3)) = (Nat.mul y2 (y0 y1 y2 y3)))) (@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) (fun y0 : type1306 => forall y1 : type1674, (forall y2 : nat, (y0 y1 y2 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y2 : nat, forall y3 : nat, (y0 y1 y2 (S y3)) = (Nat.mul y2 (y0 y1 y2 y3))))).
Definition term107 (x0 : type1306) (x1 : type1674) := (fun y0 : type1606 => (forall y1 : nat, (y0 y1 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y1 : nat, forall y2 : nat, (y0 y1 (S y2)) = (Nat.mul y1 (y0 y1 y2)))) (x0 x1).
Definition term112 (x0 : type1306) := forall y0 : type1674, (forall y1 : nat, (x0 y0 y1 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y1 : nat, forall y2 : nat, (x0 y0 y1 (S y2)) = (Nat.mul y1 (x0 y0 y1 y2))).
Definition term84 := exists y0 : type1606, (forall y1 : nat, (y0 y1 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y1 : nat, forall y2 : nat, (y0 y1 (S y2)) = (Nat.mul y1 (y0 y1 y2))).
Definition term82 := exists y0 : type1606, (forall y1 : nat, (y0 (NUMERAL 0) y1) = (NUMERAL (BIT1 0))) /\ (forall y1 : nat, forall y2 : nat, (y0 (S y2) y1) = (Nat.mul y1 (y0 y2 y1))).
Definition term76 (x0 : type1606) := forall y0 : nat, (x0 (S y0)) = ((fun y1 : nat -> nat => fun y2 : nat => fun y3 : nat => Nat.mul y3 (y1 y3)) (x0 y0) y0).
Definition term40 (x0 : type1606) (x1 : nat) (x2 : nat) := @eq nat ((fun y0 : nat => x0 y0 x1) x2).
Definition term90 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term115 := exists y0 : type1306, forall y1 : type1674, (forall y2 : nat, (y0 y1 y2 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y2 : nat, forall y3 : nat, (y0 y1 y2 (S y3)) = (Nat.mul y2 (y0 y1 y2 y3))).
Definition term95 := exists y0 : type1306, forall y1 : type1674, (fun y2 : type1674 => fun y3 : type1606 => (forall y4 : nat, (y3 y4 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y4 : nat, forall y5 : nat, (y3 y4 (S y5)) = (Nat.mul y4 (y3 y4 y5)))) y1 (y0 y1).
Definition term93 (x0 : type1300) := exists y0 : type1306, forall y1 : type1674, x0 y1 (y0 y1).
Definition term111 (x0 : type1306) := forall y0 : type1674, (fun y1 : type1674 => fun y2 : type1606 => (forall y3 : nat, (y2 y3 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y3 : nat, forall y4 : nat, (y2 y3 (S y4)) = (Nat.mul y3 (y2 y3 y4)))) y0 (x0 y0).
Definition term39 (x0 : type1606) (x1 : nat) (x2 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) x2).
Definition term117 := fun y0 : type369 => y0 (@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) y0).
Definition term68 := fun y0 : nat -> nat => fun y1 : nat => fun y2 : nat => Nat.mul y2 (y0 y2).
Definition term8 (x0 : type1606) (x1 : nat) := fun y0 : nat => x0 y0 x1.
Definition term74 (x0 : type1606) := fun y0 : nat => (x0 (S y0)) = ((fun y1 : nat -> nat => fun y2 : nat => fun y3 : nat => Nat.mul y3 (y1 y3)) (x0 y0) y0).
Definition term20 (x0 : type1606) (x1 : nat) := x0 (NUMERAL 0) x1.
Definition term35 (x0 : type1606) (x1 : nat) (x2 : nat) := x0 (S x1) x2.
Definition term62 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : type1423 a0, exists y2 : nat -> a0, ((y2 (NUMERAL 0)) = y0) /\ (forall y3 : nat, (y2 (S y3)) = (y1 (y2 y3) y3))) x0.
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => ((fun y1 : a0 => x0 y1) y0) = (x0 y0)) x1.
Definition term31 (x0 : type1606) (x1 : nat) (x2 : nat) := (fun y0 : nat => x0 y0 x1) (S x2).
Definition term18 (x0 : type1606) (x1 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) (NUMERAL 0)).
Definition term43 (x0 : type1606) (x1 : nat) := fun y0 : nat => (x0 x1 (S y0)) = (Nat.mul x1 (x0 x1 y0)).
Definition term103 := fun y0 : type1674 => exists y1 : type1606, (forall y2 : nat, (y1 y2 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y2 : nat, forall y3 : nat, (y1 y2 (S y3)) = (Nat.mul y2 (y1 y2 y3))).
Definition term34 (x0 : type1606) (x1 : nat) (x2 : nat) := @eq nat ((fun y0 : nat => x0 y0 x1) (S x2)).
Definition term19 (x0 : type1606) (x1 : nat) := @eq nat ((fun y0 : nat => x0 y0 x1) (NUMERAL 0)).
Definition term29 (x0 : type1606) := and (forall y0 : nat, (x0 (NUMERAL 0) y0) = (NUMERAL (BIT1 0))).
Definition term28 (x0 : type1606) := and (forall y0 : nat, (x0 y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))).
Definition term5 (x0 : type1606) (x1 : nat) := (fun y0 : nat => fun y1 : nat => x0 y1 y0) x1.
Definition term81 := exists y0 : type1606, ((y0 (NUMERAL 0)) = (fun y1 : nat => NUMERAL (BIT1 0))) /\ (forall y1 : nat, (y0 (S y1)) = (fun y2 : nat => Nat.mul y2 (y0 y1 y2))).
Definition term67 := exists y0 : type1606, ((y0 (NUMERAL 0)) = (fun y1 : nat => NUMERAL (BIT1 0))) /\ (forall y1 : nat, (y0 (S y1)) = ((fun y2 : nat -> nat => fun y3 : nat => fun y4 : nat => Nat.mul y4 (y2 y4)) (y0 y1) y1)).
Definition term116 (a0 : Type') := fun y0 : a0 -> Prop => y0 (@ε a0 y0).
Definition term106 (x0 : type1306) (x1 : type1674) := (fun y0 : type1674 => fun y1 : type1606 => (forall y2 : nat, (y1 y2 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y2 : nat, forall y3 : nat, (y1 y2 (S y3)) = (Nat.mul y2 (y1 y2 y3)))) x1 (x0 x1).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term61 (x0 : type1606) := ((x0 (NUMERAL 0)) = (fun y0 : nat => NUMERAL (BIT1 0))) /\ (forall y0 : nat, (x0 (S y0)) = (fun y1 : nat => Nat.mul y1 (x0 y0 y1))).
Definition term36 (x0 : type1606) (x1 : nat) (x2 : nat) := @eq nat (x0 x1 (S x2)).
Definition term118 := (fun y0 : type369 => y0 (@ε ((prod nat (prod nat nat)) -> nat -> nat -> nat) y0)) (fun y0 : type1306 => forall y1 : type1674, (forall y2 : nat, (y0 y1 y2 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y2 : nat, forall y3 : nat, (y0 y1 y2 (S y3)) = (Nat.mul y2 (y0 y1 y2 y3)))).
Definition term42 (x0 : type1606) (x1 : nat) (x2 : nat) := Nat.mul x2 (x0 x1 x2).
Definition term50 (x0 : type1606) := forall y0 : nat, forall y1 : nat, (x0 (S y1) y0) = (Nat.mul y0 (x0 y1 y0)).
Definition term49 (x0 : type1606) := forall y0 : nat, forall y1 : nat, (x0 y0 (S y1)) = (Nat.mul y0 (x0 y0 y1)).
Definition term110 (x0 : type1306) := fun y0 : type1674 => (forall y1 : nat, (x0 y0 y1 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y1 : nat, forall y2 : nat, (x0 y0 y1 (S y2)) = (Nat.mul y1 (x0 y0 y1 y2))).
Definition term14 (x0 : nat -> nat) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term6 (x0 : type1606) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term33 (x0 : type1606) (x1 : nat) (x2 : nat) := @eq nat ((fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) (S x2)).
Definition term101 (x0 : type1674) := exists y0 : type1606, (fun y1 : type1674 => fun y2 : type1606 => (forall y3 : nat, (y2 y3 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y3 : nat, forall y4 : nat, (y2 y3 (S y4)) = (Nat.mul y3 (y2 y3 y4)))) x0 y0.
Definition term85 := fun y0 : type1606 => (forall y1 : nat, (y0 y1 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y1 : nat, forall y2 : nat, (y0 y1 (S y2)) = (Nat.mul y1 (y0 y1 y2))).
Definition term83 := fun y0 : type1606 => (forall y1 : nat, (y0 (NUMERAL 0) y1) = (NUMERAL (BIT1 0))) /\ (forall y1 : nat, forall y2 : nat, (y0 (S y2) y1) = (Nat.mul y1 (y0 y2 y1))).
Definition term99 (x0 : type1606) := (fun y0 : type1606 => (forall y1 : nat, (y0 y1 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y1 : nat, forall y2 : nat, (y0 y1 (S y2)) = (Nat.mul y1 (y0 y1 y2)))) x0.
Definition term27 (x0 : type1606) := forall y0 : nat, (x0 (NUMERAL 0) y0) = (NUMERAL (BIT1 0)).
Definition term60 (x0 : type1606) (x1 : nat) (x2 : nat) := (fun y0 : nat => Nat.mul y0 (x0 x1 y0)) x2.
Definition term78 (x0 : type1606) := ((x0 (NUMERAL 0)) = (fun y0 : nat => NUMERAL (BIT1 0))) /\ (forall y0 : nat, (x0 (S y0)) = ((fun y1 : nat -> nat => fun y2 : nat => fun y3 : nat => Nat.mul y3 (y1 y3)) (x0 y0) y0)).
Definition term7 (x0 : type1606) (x1 : nat) := (fun y0 : nat => (fun y1 : nat => fun y2 : nat => x0 y2 y1) y0) x1.
Definition term13 (x0 : type1606) (x1 : nat) := (fun y0 : nat => x0 y0 x1) (NUMERAL 0).
Definition term22 (x0 : type1606) (x1 : nat) := @eq nat (x0 (NUMERAL 0) x1).
Definition term108 (x0 : type1306) (x1 : type1674) := (forall y0 : nat, (x0 x1 y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y0 : nat, forall y1 : nat, (x0 x1 y0 (S y1)) = (Nat.mul y0 (x0 x1 y0 y1))).
Definition term52 (x0 : type1606) := (forall y0 : nat, (x0 (NUMERAL 0) y0) = (NUMERAL (BIT1 0))) /\ (forall y0 : nat, forall y1 : nat, (x0 (S y1) y0) = (Nat.mul y0 (x0 y1 y0))).
Definition term51 (x0 : type1606) := (forall y0 : nat, (x0 y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y0 : nat, forall y1 : nat, (x0 y0 (S y1)) = (Nat.mul y0 (x0 y0 y1))).
Definition term109 (x0 : type1306) := fun y0 : type1674 => (fun y1 : type1674 => fun y2 : type1606 => (forall y3 : nat, (y2 y3 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y3 : nat, forall y4 : nat, (y2 y3 (S y4)) = (Nat.mul y3 (y2 y3 y4)))) y0 (x0 y0).
Definition term72 (x0 : type1606) (x1 : nat) := (fun y0 : nat => fun y1 : nat => Nat.mul y1 (x0 x1 y1)) x1.
Definition term53 (x0 : type1606) := x0 (NUMERAL 0).
Definition term12 (x0 : type1606) (x1 : nat) := x0 x1 (NUMERAL 0).
Definition term73 (x0 : type1606) (x1 : nat) := @eq (nat -> nat) (x0 (S x1)).
Definition term80 := fun y0 : type1606 => ((y0 (NUMERAL 0)) = (fun y1 : nat => NUMERAL (BIT1 0))) /\ (forall y1 : nat, (y0 (S y1)) = (fun y2 : nat => Nat.mul y2 (y0 y1 y2))).
Definition term79 := fun y0 : type1606 => ((y0 (NUMERAL 0)) = (fun y1 : nat => NUMERAL (BIT1 0))) /\ (forall y1 : nat, (y0 (S y1)) = ((fun y2 : nat -> nat => fun y3 : nat => fun y4 : nat => Nat.mul y4 (y2 y4)) (y0 y1) y1)).
Definition term26 (x0 : type1606) := forall y0 : nat, (x0 y0 (NUMERAL 0)) = (NUMERAL (BIT1 0)).
Definition term86 (x0 : type1606) (x1 : type1606) := (x0 = (fun y0 : nat => fun y1 : nat => x1 y1 y0)) -> exists y0 : type1606, (forall y1 : nat, (y0 y1 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y1 : nat, forall y2 : nat, (y0 y1 (S y2)) = (Nat.mul y1 (y0 y1 y2))).
Definition term10 (x0 : type1606) (x1 : nat) := @eq (nat -> nat) ((fun y0 : nat => (fun y1 : nat => fun y2 : nat => x0 y2 y1) y0) x1).
Definition term41 (x0 : type1606) (x1 : nat) (x2 : nat) := Nat.mul x1 (x0 x1 x2).
Definition term58 (x0 : type1606) (x1 : nat) := x0 (S x1).
Definition term46 (x0 : type1606) (x1 : nat) := forall y0 : nat, (x0 (S y0) x1) = (Nat.mul x1 (x0 y0 x1)).
Definition term63 (a0 : Type') (x0 : a0) := forall y0 : type1423 a0, exists y1 : nat -> a0, ((y1 (NUMERAL 0)) = x0) /\ (forall y2 : nat, (y1 (S y2)) = (y0 (y1 y2) y2)).
Definition term89 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => (forall y1 : a0, exists y2 : a1, y0 y1 y2) = (exists y1 : a0 -> a1, forall y2 : a0, y0 y2 (y1 y2))) x0.
Definition term59 (x0 : type1606) (x1 : nat) := fun y0 : nat => Nat.mul y0 (x0 x1 y0).
Definition term77 (x0 : type1606) := and ((x0 (NUMERAL 0)) = (fun y0 : nat => NUMERAL (BIT1 0))).
Definition term97 (x0 : type1674) := (fun y0 : type1674 => fun y1 : type1606 => (forall y2 : nat, (y1 y2 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y2 : nat, forall y3 : nat, (y1 y2 (S y3)) = (Nat.mul y2 (y1 y2 y3)))) x0.
Definition term44 (x0 : type1606) (x1 : nat) := fun y0 : nat => (x0 (S y0) x1) = (Nat.mul x1 (x0 y0 x1)).
Definition term32 (x0 : type1606) (x1 : nat) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) (S x2).
Definition term57 (x0 : type1606) (x1 : nat) := (fun y0 : nat => (x0 (S y0)) = (fun y1 : nat => Nat.mul y1 (x0 y0 y1))) x1.
Definition term91 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term66 (x0 : nat -> nat) (x1 : type1000) := exists y0 : type1606, ((y0 (NUMERAL 0)) = x0) /\ (forall y1 : nat, (y0 (S y1)) = (x1 (y0 y1) y1)).
Definition term65 (a0 : Type') (x0 : a0) (x1 : type1423 a0) := exists y0 : nat -> a0, ((y0 (NUMERAL 0)) = x0) /\ (forall y1 : nat, (y0 (S y1)) = (x1 (y0 y1) y1)).
Definition term94 := forall y0 : type1674, exists y1 : type1606, (fun y2 : type1674 => fun y3 : type1606 => (forall y4 : nat, (y3 y4 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y4 : nat, forall y5 : nat, (y3 y4 (S y5)) = (Nat.mul y4 (y3 y4 y5)))) y0 y1.
Definition term92 (x0 : type1300) := forall y0 : type1674, exists y1 : type1606, x0 y0 y1.
Definition term38 (x0 : type1606) (x1 : nat) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) x2.
Definition term37 (x0 : type1606) (x1 : nat) (x2 : nat) := @eq nat (x0 (S x1) x2).
Definition term75 (x0 : type1606) := fun y0 : nat => (x0 (S y0)) = (fun y1 : nat => Nat.mul y1 (x0 y0 y1)).
Definition term48 (x0 : type1606) := fun y0 : nat => forall y1 : nat, (x0 (S y1) y0) = (Nat.mul y0 (x0 y1 y0)).
Definition term47 (x0 : type1606) := fun y0 : nat => forall y1 : nat, (x0 y0 (S y1)) = (Nat.mul y0 (x0 y0 y1)).
Definition term87 (x0 : type1606) := ((fun y0 : nat => fun y1 : nat => x0 y1 y0) = (fun y0 : nat => fun y1 : nat => x0 y1 y0)) -> exists y0 : type1606, (forall y1 : nat, (y0 y1 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y1 : nat, forall y2 : nat, (y0 y1 (S y2)) = (Nat.mul y1 (y0 y1 y2))).
Definition term23 := NUMERAL (BIT1 0).
Definition term88 := forall y0 : type1674, exists y1 : type1606, (forall y2 : nat, (y1 y2 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y2 : nat, forall y3 : nat, (y1 y2 (S y3)) = (Nat.mul y2 (y1 y2 y3))).
Definition term21 (x0 : type1606) (x1 : nat) := @eq nat (x0 x1 (NUMERAL 0)).
Definition term70 (x0 : type1606) (x1 : nat) := fun y0 : nat => fun y1 : nat => Nat.mul y1 (x0 x1 y1).
Definition term16 (x0 : type1606) (x1 : nat) (x2 : nat) := (fun y0 : nat => x0 y0 x1) x2.
Definition term102 := fun y0 : type1674 => exists y1 : type1606, (fun y2 : type1674 => fun y3 : type1606 => (forall y4 : nat, (y3 y4 (NUMERAL 0)) = (NUMERAL (BIT1 0))) /\ (forall y4 : nat, forall y5 : nat, (y3 y4 (S y5)) = (Nat.mul y4 (y3 y4 y5)))) y0 y1.
