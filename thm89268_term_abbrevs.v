Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0, ((fun y2 : a0 => y0 y2) y1) = (y0 y1)) x0.
Definition term114 := fun y0 : type1323 => forall y1 : prod nat nat, (forall y2 : nat, (y0 y1 y2 (NUMERAL 0)) = (y2 = (NUMERAL 0))) /\ (forall y2 : nat, forall y3 : nat, (y0 y1 y2 (S y3)) = ((y2 = (S y3)) \/ (y0 y1 y2 y3))).
Definition term105 := @eq Prop (forall y0 : prod nat nat, exists y1 : type1605, (forall y2 : nat, (y1 y2 (NUMERAL 0)) = (y2 = (NUMERAL 0))) /\ (forall y2 : nat, forall y3 : nat, (y1 y2 (S y3)) = ((y2 = (S y3)) \/ (y1 y2 y3)))).
Definition term104 := @eq Prop (forall y0 : prod nat nat, exists y1 : type1605, (fun y2 : prod nat nat => fun y3 : type1605 => (forall y4 : nat, (y3 y4 (NUMERAL 0)) = (y4 = (NUMERAL 0))) /\ (forall y4 : nat, forall y5 : nat, (y3 y4 (S y5)) = ((y4 = (S y5)) \/ (y3 y4 y5)))) y0 y1).
Definition term29 (x0 : type1605) (x1 : nat) (x2 : nat) := x0 x1 (S x2).
Definition term113 := fun y0 : type1323 => forall y1 : prod nat nat, (fun y2 : prod nat nat => fun y3 : type1605 => (forall y4 : nat, (y3 y4 (NUMERAL 0)) = (y4 = (NUMERAL 0))) /\ (forall y4 : nat, forall y5 : nat, (y3 y4 (S y5)) = ((y4 = (S y5)) \/ (y3 y4 y5)))) y1 (y0 y1).
Definition term78 (x0 : type1605) := ((x0 (NUMERAL 0)) = (fun y0 : nat => y0 = (NUMERAL 0))) /\ (forall y0 : nat, (x0 (S y0)) = ((fun y1 : nat -> Prop => fun y2 : nat => fun y3 : nat => (y3 = (S y2)) \/ (y1 y3)) (x0 y0) y0)).
Definition term100 (x0 : prod nat nat) := fun y0 : type1605 => (fun y1 : prod nat nat => fun y2 : type1605 => (forall y3 : nat, (y2 y3 (NUMERAL 0)) = (y3 = (NUMERAL 0))) /\ (forall y3 : nat, forall y4 : nat, (y2 y3 (S y4)) = ((y3 = (S y4)) \/ (y2 y3 y4)))) x0 y0.
Definition term69 (x0 : type1605) (x1 : nat) := (fun y0 : nat -> Prop => fun y1 : nat => fun y2 : nat => (y2 = (S y1)) \/ (y0 y2)) (x0 x1).
Definition term4 (x0 : type1605) := fun y0 : nat => fun y1 : nat => x0 y1 y0.
Definition term70 (x0 : type1605) (x1 : nat) := fun y0 : nat => fun y1 : nat => (y1 = (S y0)) \/ (x0 x1 y1).
Definition term56 (x0 : type1605) := forall y0 : nat, (x0 (S y0)) = (fun y1 : nat => (y1 = (S y0)) \/ (x0 y0 y1)).
Definition term98 (x0 : prod nat nat) (x1 : type1605) := (fun y0 : prod nat nat => fun y1 : type1605 => (forall y2 : nat, (y1 y2 (NUMERAL 0)) = (y2 = (NUMERAL 0))) /\ (forall y2 : nat, forall y3 : nat, (y1 y2 (S y3)) = ((y2 = (S y3)) \/ (y1 y2 y3)))) x0 x1.
Definition term11 (x0 : type1605) (x1 : nat) := @eq (nat -> Prop) ((fun y0 : nat => fun y1 : nat => x0 y1 y0) x1).
Definition term38 (x0 : type1605) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) x2).
Definition term77 (x0 : type1605) := and ((x0 (NUMERAL 0)) = (fun y0 : nat => y0 = (NUMERAL 0))).
Definition term17 (x0 : type1605) (x1 : nat) := fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0.
Definition term1 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0, ((fun y1 : a0 => x0 y1) y0) = (x0 y0).
Definition term40 (x0 : nat) (x1 : nat) := or (x0 = (S x1)).
Definition term59 (x0 : type1605) (x1 : nat) := fun y0 : nat => (y0 = (S x1)) \/ (x0 x1 y0).
Definition term9 (x0 : type1605) := fun y0 : nat => (fun y1 : nat => fun y2 : nat => x0 y2 y1) y0.
Definition term64 (a0 : Type') (x0 : a0) (x1 : type1423 a0) := (fun y0 : type1423 a0 => exists y1 : nat -> a0, ((y1 (NUMERAL 0)) = x0) /\ (forall y2 : nat, (y1 (S y2)) = (y0 (y1 y2) y2))) x1.
Definition term71 (x0 : type1605) (x1 : nat) := (fun y0 : nat -> Prop => fun y1 : nat => fun y2 : nat => (y2 = (S y1)) \/ (y0 y2)) (x0 x1) x1.
Definition term15 (x0 : type1605) (x1 : nat) := (fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) (NUMERAL 0).
Definition term22 (x0 : type1605) (x1 : nat) := @eq Prop (x0 (NUMERAL 0) x1).
Definition term119 := (fun y0 : type1323 => forall y1 : prod nat nat, (forall y2 : nat, (y0 y1 y2 (NUMERAL 0)) = (y2 = (NUMERAL 0))) /\ (forall y2 : nat, forall y3 : nat, (y0 y1 y2 (S y3)) = ((y2 = (S y3)) \/ (y0 y1 y2 y3)))) (@ε ((prod nat nat) -> nat -> nat -> Prop) (fun y0 : type1323 => forall y1 : prod nat nat, (forall y2 : nat, (y0 y1 y2 (NUMERAL 0)) = (y2 = (NUMERAL 0))) /\ (forall y2 : nat, forall y3 : nat, (y0 y1 y2 (S y3)) = ((y2 = (S y3)) \/ (y0 y1 y2 y3))))).
Definition term107 (x0 : type1323) (x1 : prod nat nat) := (fun y0 : type1605 => (forall y1 : nat, (y0 y1 (NUMERAL 0)) = (y1 = (NUMERAL 0))) /\ (forall y1 : nat, forall y2 : nat, (y0 y1 (S y2)) = ((y1 = (S y2)) \/ (y0 y1 y2)))) (x0 x1).
Definition term112 (x0 : type1323) := forall y0 : prod nat nat, (forall y1 : nat, (x0 y0 y1 (NUMERAL 0)) = (y1 = (NUMERAL 0))) /\ (forall y1 : nat, forall y2 : nat, (x0 y0 y1 (S y2)) = ((y1 = (S y2)) \/ (x0 y0 y1 y2))).
Definition term84 := exists y0 : type1605, (forall y1 : nat, (y0 y1 (NUMERAL 0)) = (y1 = (NUMERAL 0))) /\ (forall y1 : nat, forall y2 : nat, (y0 y1 (S y2)) = ((y1 = (S y2)) \/ (y0 y1 y2))).
Definition term82 := exists y0 : type1605, (forall y1 : nat, (y0 (NUMERAL 0) y1) = (y1 = (NUMERAL 0))) /\ (forall y1 : nat, forall y2 : nat, (y0 (S y2) y1) = ((y1 = (S y2)) \/ (y0 y2 y1))).
Definition term76 (x0 : type1605) := forall y0 : nat, (x0 (S y0)) = ((fun y1 : nat -> Prop => fun y2 : nat => fun y3 : nat => (y3 = (S y2)) \/ (y1 y3)) (x0 y0) y0).
Definition term103 := fun y0 : prod nat nat => exists y1 : type1605, (forall y2 : nat, (y1 y2 (NUMERAL 0)) = (y2 = (NUMERAL 0))) /\ (forall y2 : nat, forall y3 : nat, (y1 y2 (S y3)) = ((y2 = (S y3)) \/ (y1 y2 y3))).
Definition term90 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, exists y1 : a1, x0 y0 y1.
Definition term115 := exists y0 : type1323, forall y1 : prod nat nat, (forall y2 : nat, (y0 y1 y2 (NUMERAL 0)) = (y2 = (NUMERAL 0))) /\ (forall y2 : nat, forall y3 : nat, (y0 y1 y2 (S y3)) = ((y2 = (S y3)) \/ (y0 y1 y2 y3))).
Definition term95 := exists y0 : type1323, forall y1 : prod nat nat, (fun y2 : prod nat nat => fun y3 : type1605 => (forall y4 : nat, (y3 y4 (NUMERAL 0)) = (y4 = (NUMERAL 0))) /\ (forall y4 : nat, forall y5 : nat, (y3 y4 (S y5)) = ((y4 = (S y5)) \/ (y3 y4 y5)))) y1 (y0 y1).
Definition term93 (x0 : type1319) := exists y0 : type1323, forall y1 : prod nat nat, x0 y1 (y0 y1).
Definition term61 (x0 : type1605) := ((x0 (NUMERAL 0)) = (fun y0 : nat => y0 = (NUMERAL 0))) /\ (forall y0 : nat, (x0 (S y0)) = (fun y1 : nat => (y1 = (S y0)) \/ (x0 y0 y1))).
Definition term111 (x0 : type1323) := forall y0 : prod nat nat, (fun y1 : prod nat nat => fun y2 : type1605 => (forall y3 : nat, (y2 y3 (NUMERAL 0)) = (y3 = (NUMERAL 0))) /\ (forall y3 : nat, forall y4 : nat, (y2 y3 (S y4)) = ((y3 = (S y4)) \/ (y2 y3 y4)))) y0 (x0 y0).
Definition term117 := fun y0 : type380 => y0 (@ε ((prod nat nat) -> nat -> nat -> Prop) y0).
Definition term68 := fun y0 : nat -> Prop => fun y1 : nat => fun y2 : nat => (y2 = (S y1)) \/ (y0 y2).
Definition term42 (x0 : type1605) (x1 : nat) (x2 : nat) := (x2 = (S x1)) \/ (x0 x1 x2).
Definition term8 (x0 : type1605) (x1 : nat) := fun y0 : nat => x0 y0 x1.
Definition term74 (x0 : type1605) := fun y0 : nat => (x0 (S y0)) = ((fun y1 : nat -> Prop => fun y2 : nat => fun y3 : nat => (y3 = (S y2)) \/ (y1 y3)) (x0 y0) y0).
Definition term20 (x0 : type1605) (x1 : nat) := x0 (NUMERAL 0) x1.
Definition term34 (x0 : type1605) (x1 : nat) (x2 : nat) := x0 (S x1) x2.
Definition term60 (x0 : type1605) (x1 : nat) (x2 : nat) := (fun y0 : nat => (y0 = (S x1)) \/ (x0 x1 y0)) x2.
Definition term62 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : type1423 a0, exists y2 : nat -> a0, ((y2 (NUMERAL 0)) = y0) /\ (forall y3 : nat, (y2 (S y3)) = (y1 (y2 y3) y3))) x0.
Definition term35 (x0 : type1605) (x1 : nat) (x2 : nat) := @eq Prop (x0 x1 (S x2)).
Definition term2 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => ((fun y1 : a0 => x0 y1) y0) = (x0 y0)) x1.
Definition term30 (x0 : type1605) (x1 : nat) (x2 : nat) := (fun y0 : nat => x0 y0 x1) (S x2).
Definition term28 (x0 : type1605) := and (forall y0 : nat, (x0 (NUMERAL 0) y0) = (y0 = (NUMERAL 0))).
Definition term27 (x0 : type1605) := and (forall y0 : nat, (x0 y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))).
Definition term5 (x0 : type1605) (x1 : nat) := (fun y0 : nat => fun y1 : nat => x0 y1 y0) x1.
Definition term81 := exists y0 : type1605, ((y0 (NUMERAL 0)) = (fun y1 : nat => y1 = (NUMERAL 0))) /\ (forall y1 : nat, (y0 (S y1)) = (fun y2 : nat => (y2 = (S y1)) \/ (y0 y1 y2))).
Definition term67 := exists y0 : type1605, ((y0 (NUMERAL 0)) = (fun y1 : nat => y1 = (NUMERAL 0))) /\ (forall y1 : nat, (y0 (S y1)) = ((fun y2 : nat -> Prop => fun y3 : nat => fun y4 : nat => (y4 = (S y3)) \/ (y2 y4)) (y0 y1) y1)).
Definition term116 (a0 : Type') := fun y0 : a0 -> Prop => y0 (@ε a0 y0).
Definition term106 (x0 : type1323) (x1 : prod nat nat) := (fun y0 : prod nat nat => fun y1 : type1605 => (forall y2 : nat, (y1 y2 (NUMERAL 0)) = (y2 = (NUMERAL 0))) /\ (forall y2 : nat, forall y3 : nat, (y1 y2 (S y3)) = ((y2 = (S y3)) \/ (y1 y2 y3)))) x1 (x0 x1).
Definition term3 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term118 := (fun y0 : type380 => y0 (@ε ((prod nat nat) -> nat -> nat -> Prop) y0)) (fun y0 : type1323 => forall y1 : prod nat nat, (forall y2 : nat, (y0 y1 y2 (NUMERAL 0)) = (y2 = (NUMERAL 0))) /\ (forall y2 : nat, forall y3 : nat, (y0 y1 y2 (S y3)) = ((y2 = (S y3)) \/ (y0 y1 y2 y3)))).
Definition term50 (x0 : type1605) := forall y0 : nat, forall y1 : nat, (x0 (S y1) y0) = ((y0 = (S y1)) \/ (x0 y1 y0)).
Definition term49 (x0 : type1605) := forall y0 : nat, forall y1 : nat, (x0 y0 (S y1)) = ((y0 = (S y1)) \/ (x0 y0 y1)).
Definition term110 (x0 : type1323) := fun y0 : prod nat nat => (forall y1 : nat, (x0 y0 y1 (NUMERAL 0)) = (y1 = (NUMERAL 0))) /\ (forall y1 : nat, forall y2 : nat, (x0 y0 y1 (S y2)) = ((y1 = (S y2)) \/ (x0 y0 y1 y2))).
Definition term14 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term6 (x0 : type1605) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term101 (x0 : prod nat nat) := exists y0 : type1605, (fun y1 : prod nat nat => fun y2 : type1605 => (forall y3 : nat, (y2 y3 (NUMERAL 0)) = (y3 = (NUMERAL 0))) /\ (forall y3 : nat, forall y4 : nat, (y2 y3 (S y4)) = ((y3 = (S y4)) \/ (y2 y3 y4)))) x0 y0.
Definition term85 := fun y0 : type1605 => (forall y1 : nat, (y0 y1 (NUMERAL 0)) = (y1 = (NUMERAL 0))) /\ (forall y1 : nat, forall y2 : nat, (y0 y1 (S y2)) = ((y1 = (S y2)) \/ (y0 y1 y2))).
Definition term83 := fun y0 : type1605 => (forall y1 : nat, (y0 (NUMERAL 0) y1) = (y1 = (NUMERAL 0))) /\ (forall y1 : nat, forall y2 : nat, (y0 (S y2) y1) = ((y1 = (S y2)) \/ (y0 y2 y1))).
Definition term23 (x0 : type1605) := fun y0 : nat => (x0 y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term99 (x0 : type1605) := (fun y0 : type1605 => (forall y1 : nat, (y0 y1 (NUMERAL 0)) = (y1 = (NUMERAL 0))) /\ (forall y1 : nat, forall y2 : nat, (y0 y1 (S y2)) = ((y1 = (S y2)) \/ (y0 y1 y2)))) x0.
Definition term45 (x0 : type1605) (x1 : nat) := forall y0 : nat, (x0 x1 (S y0)) = ((x1 = (S y0)) \/ (x0 x1 y0)).
Definition term43 (x0 : type1605) (x1 : nat) := fun y0 : nat => (x0 x1 (S y0)) = ((x1 = (S y0)) \/ (x0 x1 y0)).
Definition term18 (x0 : type1605) (x1 : nat) := @eq Prop ((fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) (NUMERAL 0)).
Definition term75 (x0 : type1605) := fun y0 : nat => (x0 (S y0)) = (fun y1 : nat => (y1 = (S y0)) \/ (x0 y0 y1)).
Definition term41 (x0 : type1605) (x1 : nat) (x2 : nat) := (x1 = (S x2)) \/ (x0 x1 x2).
Definition term7 (x0 : type1605) (x1 : nat) := (fun y0 : nat => (fun y1 : nat => fun y2 : nat => x0 y2 y1) y0) x1.
Definition term13 (x0 : type1605) (x1 : nat) := (fun y0 : nat => x0 y0 x1) (NUMERAL 0).
Definition term108 (x0 : type1323) (x1 : prod nat nat) := (forall y0 : nat, (x0 x1 y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (x0 x1 y0 (S y1)) = ((y0 = (S y1)) \/ (x0 x1 y0 y1))).
Definition term52 (x0 : type1605) := (forall y0 : nat, (x0 (NUMERAL 0) y0) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (x0 (S y1) y0) = ((y0 = (S y1)) \/ (x0 y1 y0))).
Definition term51 (x0 : type1605) := (forall y0 : nat, (x0 y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) /\ (forall y0 : nat, forall y1 : nat, (x0 y0 (S y1)) = ((y0 = (S y1)) \/ (x0 y0 y1))).
Definition term72 (x0 : type1605) (x1 : nat) := (fun y0 : nat => fun y1 : nat => (y1 = (S y0)) \/ (x0 x1 y1)) x1.
Definition term109 (x0 : type1323) := fun y0 : prod nat nat => (fun y1 : prod nat nat => fun y2 : type1605 => (forall y3 : nat, (y2 y3 (NUMERAL 0)) = (y3 = (NUMERAL 0))) /\ (forall y3 : nat, forall y4 : nat, (y2 y3 (S y4)) = ((y3 = (S y4)) \/ (y2 y3 y4)))) y0 (x0 y0).
Definition term55 (x0 : nat) := (fun y0 : nat => y0 = (NUMERAL 0)) x0.
Definition term39 (x0 : type1605) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : nat => x0 y0 x1) x2).
Definition term36 (x0 : type1605) (x1 : nat) (x2 : nat) := @eq Prop (x0 (S x1) x2).
Definition term53 (x0 : type1605) := x0 (NUMERAL 0).
Definition term12 (x0 : type1605) (x1 : nat) := x0 x1 (NUMERAL 0).
Definition term73 (x0 : type1605) (x1 : nat) := @eq (nat -> Prop) (x0 (S x1)).
Definition term96 := fun y0 : prod nat nat => fun y1 : type1605 => (forall y2 : nat, (y1 y2 (NUMERAL 0)) = (y2 = (NUMERAL 0))) /\ (forall y2 : nat, forall y3 : nat, (y1 y2 (S y3)) = ((y2 = (S y3)) \/ (y1 y2 y3))).
Definition term80 := fun y0 : type1605 => ((y0 (NUMERAL 0)) = (fun y1 : nat => y1 = (NUMERAL 0))) /\ (forall y1 : nat, (y0 (S y1)) = (fun y2 : nat => (y2 = (S y1)) \/ (y0 y1 y2))).
Definition term79 := fun y0 : type1605 => ((y0 (NUMERAL 0)) = (fun y1 : nat => y1 = (NUMERAL 0))) /\ (forall y1 : nat, (y0 (S y1)) = ((fun y2 : nat -> Prop => fun y3 : nat => fun y4 : nat => (y4 = (S y3)) \/ (y2 y4)) (y0 y1) y1)).
Definition term44 (x0 : type1605) (x1 : nat) := fun y0 : nat => (x0 (S y0) x1) = ((x1 = (S y0)) \/ (x0 y0 x1)).
Definition term86 (x0 : type1605) (x1 : type1605) := (x0 = (fun y0 : nat => fun y1 : nat => x1 y1 y0)) -> exists y0 : type1605, (forall y1 : nat, (y0 y1 (NUMERAL 0)) = (y1 = (NUMERAL 0))) /\ (forall y1 : nat, forall y2 : nat, (y0 y1 (S y2)) = ((y1 = (S y2)) \/ (y0 y1 y2))).
Definition term46 (x0 : type1605) (x1 : nat) := forall y0 : nat, (x0 (S y0) x1) = ((x1 = (S y0)) \/ (x0 y0 x1)).
Definition term25 (x0 : type1605) := forall y0 : nat, (x0 y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term32 (x0 : type1605) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) (S x2)).
Definition term10 (x0 : type1605) (x1 : nat) := @eq (nat -> Prop) ((fun y0 : nat => (fun y1 : nat => fun y2 : nat => x0 y2 y1) y0) x1).
Definition term24 (x0 : type1605) := fun y0 : nat => (x0 (NUMERAL 0) y0) = (y0 = (NUMERAL 0)).
Definition term33 (x0 : type1605) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : nat => x0 y0 x1) (S x2)).
Definition term58 (x0 : type1605) (x1 : nat) := x0 (S x1).
Definition term63 (a0 : Type') (x0 : a0) := forall y0 : type1423 a0, exists y1 : nat -> a0, ((y1 (NUMERAL 0)) = x0) /\ (forall y2 : nat, (y1 (S y2)) = (y0 (y1 y2) y2)).
Definition term89 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => (forall y1 : a0, exists y2 : a1, y0 y1 y2) = (exists y1 : a0 -> a1, forall y2 : a0, y0 y2 (y1 y2))) x0.
Definition term54 := fun y0 : nat => y0 = (NUMERAL 0).
Definition term97 (x0 : prod nat nat) := (fun y0 : prod nat nat => fun y1 : type1605 => (forall y2 : nat, (y1 y2 (NUMERAL 0)) = (y2 = (NUMERAL 0))) /\ (forall y2 : nat, forall y3 : nat, (y1 y2 (S y3)) = ((y2 = (S y3)) \/ (y1 y2 y3)))) x0.
Definition term19 (x0 : type1605) (x1 : nat) := @eq Prop ((fun y0 : nat => x0 y0 x1) (NUMERAL 0)).
Definition term26 (x0 : type1605) := forall y0 : nat, (x0 (NUMERAL 0) y0) = (y0 = (NUMERAL 0)).
Definition term31 (x0 : type1605) (x1 : nat) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) (S x2).
Definition term57 (x0 : type1605) (x1 : nat) := (fun y0 : nat => (x0 (S y0)) = (fun y1 : nat => (y1 = (S y0)) \/ (x0 y0 y1))) x1.
Definition term91 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := exists y0 : a0 -> a1, forall y1 : a0, x0 y1 (y0 y1).
Definition term66 (x0 : nat -> Prop) (x1 : type990) := exists y0 : type1605, ((y0 (NUMERAL 0)) = x0) /\ (forall y1 : nat, (y0 (S y1)) = (x1 (y0 y1) y1)).
Definition term65 (a0 : Type') (x0 : a0) (x1 : type1423 a0) := exists y0 : nat -> a0, ((y0 (NUMERAL 0)) = x0) /\ (forall y1 : nat, (y0 (S y1)) = (x1 (y0 y1) y1)).
Definition term94 := forall y0 : prod nat nat, exists y1 : type1605, (fun y2 : prod nat nat => fun y3 : type1605 => (forall y4 : nat, (y3 y4 (NUMERAL 0)) = (y4 = (NUMERAL 0))) /\ (forall y4 : nat, forall y5 : nat, (y3 y4 (S y5)) = ((y4 = (S y5)) \/ (y3 y4 y5)))) y0 y1.
Definition term92 (x0 : type1319) := forall y0 : prod nat nat, exists y1 : type1605, x0 y0 y1.
Definition term37 (x0 : type1605) (x1 : nat) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => x0 y1 x1) y0) x2.
Definition term48 (x0 : type1605) := fun y0 : nat => forall y1 : nat, (x0 (S y1) y0) = ((y0 = (S y1)) \/ (x0 y1 y0)).
Definition term47 (x0 : type1605) := fun y0 : nat => forall y1 : nat, (x0 y0 (S y1)) = ((y0 = (S y1)) \/ (x0 y0 y1)).
Definition term87 (x0 : type1605) := ((fun y0 : nat => fun y1 : nat => x0 y1 y0) = (fun y0 : nat => fun y1 : nat => x0 y1 y0)) -> exists y0 : type1605, (forall y1 : nat, (y0 y1 (NUMERAL 0)) = (y1 = (NUMERAL 0))) /\ (forall y1 : nat, forall y2 : nat, (y0 y1 (S y2)) = ((y1 = (S y2)) \/ (y0 y1 y2))).
Definition term88 := forall y0 : prod nat nat, exists y1 : type1605, (forall y2 : nat, (y1 y2 (NUMERAL 0)) = (y2 = (NUMERAL 0))) /\ (forall y2 : nat, forall y3 : nat, (y1 y2 (S y3)) = ((y2 = (S y3)) \/ (y1 y2 y3))).
Definition term16 (x0 : type1605) (x1 : nat) (x2 : nat) := (fun y0 : nat => x0 y0 x1) x2.
Definition term21 (x0 : type1605) (x1 : nat) := @eq Prop (x0 x1 (NUMERAL 0)).
Definition term102 := fun y0 : prod nat nat => exists y1 : type1605, (fun y2 : prod nat nat => fun y3 : type1605 => (forall y4 : nat, (y3 y4 (NUMERAL 0)) = (y4 = (NUMERAL 0))) /\ (forall y4 : nat, forall y5 : nat, (y3 y4 (S y5)) = ((y4 = (S y5)) \/ (y3 y4 y5)))) y0 y1.
