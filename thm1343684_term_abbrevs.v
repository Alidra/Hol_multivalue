Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term8 (x0 : type1608) (x1 : real) := fun y0 : nat => x0 y0 x1.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0, ((fun y2 : a0 => y0 y2) y1) = (y0 y1)) x0.
Definition term114 := fun y0 : type1250 => forall y1 : type1669, (forall y2 : real, (y0 y1 y2 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y2 : real, forall y3 : nat, (y0 y1 y2 (S y3)) = (real_mul y2 (y0 y1 y2 y3))).
Definition term105 := @eq Prop (forall y0 : type1669, exists y1 : type1623, (forall y2 : real, (y1 y2 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y2 : real, forall y3 : nat, (y1 y2 (S y3)) = (real_mul y2 (y1 y2 y3)))).
Definition term104 := @eq Prop (forall y0 : type1669, exists y1 : type1623, (fun y2 : type1669 => fun y3 : type1623 => (forall y4 : real, (y3 y4 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y4 : real, forall y5 : nat, (y3 y4 (S y5)) = (real_mul y4 (y3 y4 y5)))) y0 y1).
Definition term60 (x0 : type1608) (x1 : nat) (x2 : real) := (fun y0 : real => real_mul y0 (x0 x1 y0)) x2.
Definition term7 (x0 : type1608) (x1 : real) := (fun y0 : real => (fun y1 : real => fun y2 : nat => x0 y2 y1) y0) x1.
Definition term43 (x0 : type1623) (x1 : real) := fun y0 : nat => (x0 x1 (S y0)) = (real_mul x1 (x0 x1 y0)).
Definition term113 := fun y0 : type1250 => forall y1 : type1669, (fun y2 : type1669 => fun y3 : type1623 => (forall y4 : real, (y3 y4 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y4 : real, forall y5 : nat, (y3 y4 (S y5)) = (real_mul y4 (y3 y4 y5)))) y1 (y0 y1).
Definition term19 (x0 : type1608) (x1 : real) := @eq real ((fun y0 : nat => x0 y0 x1) (NUMERAL 0)).
Definition term25 (x0 : type1608) := fun y0 : real => (x0 (NUMERAL 0) y0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term69 (x0 : type1608) (x1 : nat) := (fun y0 : real -> real => fun y1 : nat => fun y2 : real => real_mul y2 (y0 y2)) (x0 x1).
Definition term44 (x0 : type1608) (x1 : real) := fun y0 : nat => (x0 (S y0) x1) = (real_mul x1 (x0 y0 x1)).
Definition term56 (x0 : type1608) := forall y0 : nat, (x0 (S y0)) = (fun y1 : real => real_mul y1 (x0 y0 y1)).
Definition term96 := fun y0 : type1669 => fun y1 : type1623 => (forall y2 : real, (y1 y2 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y2 : real, forall y3 : nat, (y1 y2 (S y3)) = (real_mul y2 (y1 y2 y3))).
Definition term5 (x0 : type1608) (x1 : real) := (fun y0 : real => fun y1 : nat => x0 y1 y0) x1.
Definition term29 (x0 : type1608) := and (forall y0 : real, (x0 (NUMERAL 0) y0) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term28 (x0 : type1623) := and (forall y0 : real, (x0 y0 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term17 (x0 : type1608) (x1 : real) := fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0, ((fun y1 : a0 => x0 y1) y0) = (x0 y0).
Definition term48 (x0 : type1608) := fun y0 : real => forall y1 : nat, (x0 (S y1) y0) = (real_mul y0 (x0 y1 y0)).
Definition term47 (x0 : type1623) := fun y0 : real => forall y1 : nat, (x0 y0 (S y1)) = (real_mul y0 (x0 y0 y1)).
Definition term45 (x0 : type1623) (x1 : real) := forall y0 : nat, (x0 x1 (S y0)) = (real_mul x1 (x0 x1 y0)).
Definition term35 (x0 : type1608) (x1 : nat) (x2 : real) := x0 (S x1) x2.
Definition term64 (a0 : Type') (x0 : a0) (x1 : type1423 a0) := (fun y0 : type1423 a0 => exists y1 : nat -> a0, ((y1 (NUMERAL 0)) = x0) /\ (forall y2 : nat, (y1 (S y2)) = (y0 (y1 y2) y2))) x1.
Definition term16 (x0 : type1608) (x1 : real) (x2 : nat) := (fun y0 : nat => x0 y0 x1) x2.
Definition term71 (x0 : type1608) (x1 : nat) := (fun y0 : real -> real => fun y1 : nat => fun y2 : real => real_mul y2 (y0 y2)) (x0 x1) x1.
Definition term15 (x0 : type1608) (x1 : real) := (fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) (NUMERAL 0).
Definition term26 (x0 : type1623) := forall y0 : real, (x0 y0 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0))).
Definition term55 (x0 : real) := (fun y0 : real => real_of_num (NUMERAL (BIT1 0))) x0.
Definition term12 (x0 : type1623) (x1 : real) := x0 x1 (NUMERAL 0).
Definition term119 := (fun y0 : type1250 => forall y1 : type1669, (forall y2 : real, (y0 y1 y2 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y2 : real, forall y3 : nat, (y0 y1 y2 (S y3)) = (real_mul y2 (y0 y1 y2 y3)))) (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> real -> nat -> real) (fun y0 : type1250 => forall y1 : type1669, (forall y2 : real, (y0 y1 y2 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y2 : real, forall y3 : nat, (y0 y1 y2 (S y3)) = (real_mul y2 (y0 y1 y2 y3))))).
Definition term112 (x0 : type1250) := forall y0 : type1669, (forall y1 : real, (x0 y0 y1 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y1 : real, forall y2 : nat, (x0 y0 y1 (S y2)) = (real_mul y1 (x0 y0 y1 y2))).
Definition term84 := exists y0 : type1623, (forall y1 : real, (y0 y1 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y1 : real, forall y2 : nat, (y0 y1 (S y2)) = (real_mul y1 (y0 y1 y2))).
Definition term82 := exists y0 : type1608, (forall y1 : real, (y0 (NUMERAL 0) y1) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y1 : real, forall y2 : nat, (y0 (S y2) y1) = (real_mul y1 (y0 y2 y1))).
Definition term76 (x0 : type1608) := forall y0 : nat, (x0 (S y0)) = ((fun y1 : real -> real => fun y2 : nat => fun y3 : real => real_mul y3 (y1 y3)) (x0 y0) y0).
Definition term77 (x0 : type1608) := and ((x0 (NUMERAL 0)) = (fun y0 : real => real_of_num (NUMERAL (BIT1 0)))).
Definition term40 (x0 : type1608) (x1 : real) (x2 : nat) := @eq real ((fun y0 : nat => x0 y0 x1) x2).
Definition term72 (x0 : type1608) (x1 : nat) := (fun y0 : nat => fun y1 : real => real_mul y1 (x0 x1 y1)) x1.
Definition term11 (x0 : type1608) (x1 : real) := @eq (nat -> real) ((fun y0 : real => fun y1 : nat => x0 y1 y0) x1).
Definition term90 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term50 (x0 : type1608) := forall y0 : real, forall y1 : nat, (x0 (S y1) y0) = (real_mul y0 (x0 y1 y0)).
Definition term49 (x0 : type1623) := forall y0 : real, forall y1 : nat, (x0 y0 (S y1)) = (real_mul y0 (x0 y0 y1)).
Definition term115 := exists y0 : type1250, forall y1 : type1669, (forall y2 : real, (y0 y1 y2 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y2 : real, forall y3 : nat, (y0 y1 y2 (S y3)) = (real_mul y2 (y0 y1 y2 y3))).
Definition term95 := exists y0 : type1250, forall y1 : type1669, (fun y2 : type1669 => fun y3 : type1623 => (forall y4 : real, (y3 y4 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y4 : real, forall y5 : nat, (y3 y4 (S y5)) = (real_mul y4 (y3 y4 y5)))) y1 (y0 y1).
Definition term93 (x0 : type1247) := exists y0 : type1250, forall y1 : type1669, x0 y1 (y0 y1).
Definition term111 (x0 : type1250) := forall y0 : type1669, (fun y1 : type1669 => fun y2 : type1623 => (forall y3 : real, (y2 y3 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y3 : real, forall y4 : nat, (y2 y3 (S y4)) = (real_mul y3 (y2 y3 y4)))) y0 (x0 y0).
Definition term117 := fun y0 : type342 => y0 (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> real -> nat -> real) y0).
Definition term74 (x0 : type1608) := fun y0 : nat => (x0 (S y0)) = ((fun y1 : real -> real => fun y2 : nat => fun y3 : real => real_mul y3 (y1 y3)) (x0 y0) y0).
Definition term62 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : type1423 a0, exists y2 : nat -> a0, ((y2 (NUMERAL 0)) = y0) /\ (forall y3 : nat, (y2 (S y3)) = (y1 (y2 y3) y3))) x0.
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => ((fun y1 : a0 => x0 y1) y0) = (x0 y0)) x1.
Definition term9 (x0 : type1608) := fun y0 : real => (fun y1 : real => fun y2 : nat => x0 y2 y1) y0.
Definition term20 (x0 : type1608) (x1 : real) := x0 (NUMERAL 0) x1.
Definition term24 (x0 : type1623) := fun y0 : real => (x0 y0 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0))).
Definition term31 (x0 : type1608) (x1 : real) (x2 : nat) := (fun y0 : nat => x0 y0 x1) (S x2).
Definition term103 := fun y0 : type1669 => exists y1 : type1623, (forall y2 : real, (y1 y2 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y2 : real, forall y3 : nat, (y1 y2 (S y3)) = (real_mul y2 (y1 y2 y3))).
Definition term107 (x0 : type1250) (x1 : type1669) := (fun y0 : type1623 => (forall y1 : real, (y0 y1 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y1 : real, forall y2 : nat, (y0 y1 (S y2)) = (real_mul y1 (y0 y1 y2)))) (x0 x1).
Definition term81 := exists y0 : type1608, ((y0 (NUMERAL 0)) = (fun y1 : real => real_of_num (NUMERAL (BIT1 0)))) /\ (forall y1 : nat, (y0 (S y1)) = (fun y2 : real => real_mul y2 (y0 y1 y2))).
Definition term67 := exists y0 : type1608, ((y0 (NUMERAL 0)) = (fun y1 : real => real_of_num (NUMERAL (BIT1 0)))) /\ (forall y1 : nat, (y0 (S y1)) = ((fun y2 : real -> real => fun y3 : nat => fun y4 : real => real_mul y4 (y2 y4)) (y0 y1) y1)).
Definition term116 (a0 : Type') := fun y0 : a0 -> Prop => y0 (@ε a0 y0).
Definition term106 (x0 : type1250) (x1 : type1669) := (fun y0 : type1669 => fun y1 : type1623 => (forall y2 : real, (y1 y2 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y2 : real, forall y3 : nat, (y1 y2 (S y3)) = (real_mul y2 (y1 y2 y3)))) x1 (x0 x1).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term61 (x0 : type1608) := ((x0 (NUMERAL 0)) = (fun y0 : real => real_of_num (NUMERAL (BIT1 0)))) /\ (forall y0 : nat, (x0 (S y0)) = (fun y1 : real => real_mul y1 (x0 y0 y1))).
Definition term118 := (fun y0 : type342 => y0 (@ε ((prod nat (prod nat (prod nat (prod nat (prod nat (prod nat (prod nat nat))))))) -> real -> nat -> real) y0)) (fun y0 : type1250 => forall y1 : type1669, (forall y2 : real, (y0 y1 y2 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y2 : real, forall y3 : nat, (y0 y1 y2 (S y3)) = (real_mul y2 (y0 y1 y2 y3)))).
Definition term34 (x0 : type1608) (x1 : real) (x2 : nat) := @eq real ((fun y0 : nat => x0 y0 x1) (S x2)).
Definition term110 (x0 : type1250) := fun y0 : type1669 => (forall y1 : real, (x0 y0 y1 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y1 : real, forall y2 : nat, (x0 y0 y1 (S y2)) = (real_mul y1 (x0 y0 y1 y2))).
Definition term39 (x0 : type1608) (x1 : real) (x2 : nat) := @eq real ((fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) x2).
Definition term14 (x0 : nat -> real) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term59 (x0 : type1608) (x1 : nat) := fun y0 : real => real_mul y0 (x0 x1 y0).
Definition term101 (x0 : type1669) := exists y0 : type1623, (fun y1 : type1669 => fun y2 : type1623 => (forall y3 : real, (y2 y3 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y3 : real, forall y4 : nat, (y2 y3 (S y4)) = (real_mul y3 (y2 y3 y4)))) x0 y0.
Definition term83 := fun y0 : type1608 => (forall y1 : real, (y0 (NUMERAL 0) y1) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y1 : real, forall y2 : nat, (y0 (S y2) y1) = (real_mul y1 (y0 y2 y1))).
Definition term6 (x0 : type1623) (x1 : real) := (fun y0 : real => x0 y0) x1.
Definition term108 (x0 : type1250) (x1 : type1669) := (forall y0 : real, (x0 x1 y0 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y0 : real, forall y1 : nat, (x0 x1 y0 (S y1)) = (real_mul y0 (x0 x1 y0 y1))).
Definition term52 (x0 : type1608) := (forall y0 : real, (x0 (NUMERAL 0) y0) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y0 : real, forall y1 : nat, (x0 (S y1) y0) = (real_mul y0 (x0 y1 y0))).
Definition term51 (x0 : type1623) := (forall y0 : real, (x0 y0 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y0 : real, forall y1 : nat, (x0 y0 (S y1)) = (real_mul y0 (x0 y0 y1))).
Definition term75 (x0 : type1608) := fun y0 : nat => (x0 (S y0)) = (fun y1 : real => real_mul y1 (x0 y0 y1)).
Definition term10 (x0 : type1608) (x1 : real) := @eq (nat -> real) ((fun y0 : real => (fun y1 : real => fun y2 : nat => x0 y2 y1) y0) x1).
Definition term78 (x0 : type1608) := ((x0 (NUMERAL 0)) = (fun y0 : real => real_of_num (NUMERAL (BIT1 0)))) /\ (forall y0 : nat, (x0 (S y0)) = ((fun y1 : real -> real => fun y2 : nat => fun y3 : real => real_mul y3 (y1 y3)) (x0 y0) y0)).
Definition term4 (x0 : type1608) := fun y0 : real => fun y1 : nat => x0 y1 y0.
Definition term22 (x0 : type1608) (x1 : real) := @eq real (x0 (NUMERAL 0) x1).
Definition term54 := fun y0 : real => real_of_num (NUMERAL (BIT1 0)).
Definition term13 (x0 : type1608) (x1 : real) := (fun y0 : nat => x0 y0 x1) (NUMERAL 0).
Definition term30 (x0 : type1623) (x1 : real) (x2 : nat) := x0 x1 (S x2).
Definition term70 (x0 : type1608) (x1 : nat) := fun y0 : nat => fun y1 : real => real_mul y1 (x0 x1 y1).
Definition term109 (x0 : type1250) := fun y0 : type1669 => (fun y1 : type1669 => fun y2 : type1623 => (forall y3 : real, (y2 y3 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y3 : real, forall y4 : nat, (y2 y3 (S y4)) = (real_mul y3 (y2 y3 y4)))) y0 (x0 y0).
Definition term85 := fun y0 : type1623 => (forall y1 : real, (y0 y1 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y1 : real, forall y2 : nat, (y0 y1 (S y2)) = (real_mul y1 (y0 y1 y2))).
Definition term68 := fun y0 : real -> real => fun y1 : nat => fun y2 : real => real_mul y2 (y0 y2).
Definition term53 (x0 : type1608) := x0 (NUMERAL 0).
Definition term73 (x0 : type1608) (x1 : nat) := @eq (real -> real) (x0 (S x1)).
Definition term80 := fun y0 : type1608 => ((y0 (NUMERAL 0)) = (fun y1 : real => real_of_num (NUMERAL (BIT1 0)))) /\ (forall y1 : nat, (y0 (S y1)) = (fun y2 : real => real_mul y2 (y0 y1 y2))).
Definition term79 := fun y0 : type1608 => ((y0 (NUMERAL 0)) = (fun y1 : real => real_of_num (NUMERAL (BIT1 0)))) /\ (forall y1 : nat, (y0 (S y1)) = ((fun y2 : real -> real => fun y3 : nat => fun y4 : real => real_mul y4 (y2 y4)) (y0 y1) y1)).
Definition term42 (x0 : type1608) (x1 : nat) (x2 : real) := real_mul x2 (x0 x1 x2).
Definition term86 (x0 : type1623) (x1 : type1608) := (x0 = (fun y0 : real => fun y1 : nat => x1 y1 y0)) -> exists y0 : type1623, (forall y1 : real, (y0 y1 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y1 : real, forall y2 : nat, (y0 y1 (S y2)) = (real_mul y1 (y0 y1 y2))).
Definition term99 (x0 : type1623) := (fun y0 : type1623 => (forall y1 : real, (y0 y1 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y1 : real, forall y2 : nat, (y0 y1 (S y2)) = (real_mul y1 (y0 y1 y2)))) x0.
Definition term37 (x0 : type1608) (x1 : nat) (x2 : real) := @eq real (x0 (S x1) x2).
Definition term23 := real_of_num (NUMERAL (BIT1 0)).
Definition term41 (x0 : type1623) (x1 : real) (x2 : nat) := real_mul x1 (x0 x1 x2).
Definition term18 (x0 : type1608) (x1 : real) := @eq real ((fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) (NUMERAL 0)).
Definition term21 (x0 : type1623) (x1 : real) := @eq real (x0 x1 (NUMERAL 0)).
Definition term58 (x0 : type1608) (x1 : nat) := x0 (S x1).
Definition term46 (x0 : type1608) (x1 : real) := forall y0 : nat, (x0 (S y0) x1) = (real_mul x1 (x0 y0 x1)).
Definition term63 (a0 : Type') (x0 : a0) := forall y0 : type1423 a0, exists y1 : nat -> a0, ((y1 (NUMERAL 0)) = x0) /\ (forall y2 : nat, (y1 (S y2)) = (y0 (y1 y2) y2)).
Definition term89 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => (forall y1 : a0, exists y2 : a1, y0 y1 y2) = (exists y1 : a0 -> a1, forall y2 : a0, y0 y2 (y1 y2))) x0.
Definition term97 (x0 : type1669) := (fun y0 : type1669 => fun y1 : type1623 => (forall y2 : real, (y1 y2 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y2 : real, forall y3 : nat, (y1 y2 (S y3)) = (real_mul y2 (y1 y2 y3)))) x0.
Definition term98 (x0 : type1669) (x1 : type1623) := (fun y0 : type1669 => fun y1 : type1623 => (forall y2 : real, (y1 y2 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y2 : real, forall y3 : nat, (y1 y2 (S y3)) = (real_mul y2 (y1 y2 y3)))) x0 x1.
Definition term36 (x0 : type1623) (x1 : real) (x2 : nat) := @eq real (x0 x1 (S x2)).
Definition term27 (x0 : type1608) := forall y0 : real, (x0 (NUMERAL 0) y0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term32 (x0 : type1608) (x1 : real) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) (S x2).
Definition term57 (x0 : type1608) (x1 : nat) := (fun y0 : nat => (x0 (S y0)) = (fun y1 : real => real_mul y1 (x0 y0 y1))) x1.
Definition term91 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term66 (x0 : real -> real) (x1 : type1027) := exists y0 : type1608, ((y0 (NUMERAL 0)) = x0) /\ (forall y1 : nat, (y0 (S y1)) = (x1 (y0 y1) y1)).
Definition term65 (a0 : Type') (x0 : a0) (x1 : type1423 a0) := exists y0 : nat -> a0, ((y0 (NUMERAL 0)) = x0) /\ (forall y1 : nat, (y0 (S y1)) = (x1 (y0 y1) y1)).
Definition term94 := forall y0 : type1669, exists y1 : type1623, (fun y2 : type1669 => fun y3 : type1623 => (forall y4 : real, (y3 y4 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y4 : real, forall y5 : nat, (y3 y4 (S y5)) = (real_mul y4 (y3 y4 y5)))) y0 y1.
Definition term92 (x0 : type1247) := forall y0 : type1669, exists y1 : type1623, x0 y0 y1.
Definition term38 (x0 : type1608) (x1 : real) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) x2.
Definition term33 (x0 : type1608) (x1 : real) (x2 : nat) := @eq real ((fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) (S x2)).
Definition term100 (x0 : type1669) := fun y0 : type1623 => (fun y1 : type1669 => fun y2 : type1623 => (forall y3 : real, (y2 y3 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y3 : real, forall y4 : nat, (y2 y3 (S y4)) = (real_mul y3 (y2 y3 y4)))) x0 y0.
Definition term87 (x0 : type1608) := ((fun y0 : real => fun y1 : nat => x0 y1 y0) = (fun y0 : real => fun y1 : nat => x0 y1 y0)) -> exists y0 : type1623, (forall y1 : real, (y0 y1 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y1 : real, forall y2 : nat, (y0 y1 (S y2)) = (real_mul y1 (y0 y1 y2))).
Definition term88 := forall y0 : type1669, exists y1 : type1623, (forall y2 : real, (y1 y2 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y2 : real, forall y3 : nat, (y1 y2 (S y3)) = (real_mul y2 (y1 y2 y3))).
Definition term102 := fun y0 : type1669 => exists y1 : type1623, (fun y2 : type1669 => fun y3 : type1623 => (forall y4 : real, (y3 y4 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y4 : real, forall y5 : nat, (y3 y4 (S y5)) = (real_mul y4 (y3 y4 y5)))) y0 y1.
