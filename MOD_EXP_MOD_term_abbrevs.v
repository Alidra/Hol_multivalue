Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term6 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := ((x1 = x0) /\ (x0 = x2)) -> x1 = x2.
Definition term14 (a0 : Type') := (forall y0 : a0, forall y1 : a0, forall y2 : a0, ((y0 = y1) /\ (y1 = y2)) -> y0 = y2) -> forall y0 : a0, forall y1 : a0, (exists y2 : a0, (y0 = y2) /\ (y2 = y1)) -> y0 = y1.
Definition term37 (x0 : nat) (x1 : nat) := and ((Nat.modulo (Nat.pow (Nat.modulo x0 x1) (NUMERAL 0)) x1) = (Nat.modulo (Nat.pow x0 (NUMERAL 0)) x1)).
Definition term21 (x0 : nat) (x1 : nat) := Nat.pow (Nat.modulo x0 x1).
Definition term101 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.mul x0 (Nat.modulo (Nat.pow x0 x1) x2)) x2.
Definition term100 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.mul x0 (Nat.modulo (Nat.pow (Nat.modulo x0 x2) x1) x2)) x2.
Definition term24 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.pow x0 x1).
Definition term104 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.mul y0 (Nat.modulo y2 y1)) y1) = (Nat.modulo (Nat.mul y0 y2) y1)) x0.
Definition term85 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.mul (Nat.modulo y0 y1) y2) y1) = (Nat.modulo (Nat.mul y0 y2) y1)) x0.
Definition term7 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := (x0 = x1) /\ (x1 = x2).
Definition term64 := Nat.modulo (NUMERAL (BIT1 0)).
Definition term92 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.mul x0 (Nat.pow (Nat.modulo x0 x2) x1)) x2.
Definition term20 (x0 : nat) := Nat.modulo x0 (NUMERAL 0).
Definition term91 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.mul x0 x1) x2.
Definition term71 (x0 : nat) := forall y0 : nat, (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0)).
Definition term55 (x0 : nat) (x1 : nat) := forall y0 : nat, (fun y1 : nat => (Nat.modulo (Nat.pow (Nat.modulo x0 x1) y1) x1) = (Nat.modulo (Nat.pow x0 y1) x1)) y0.
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.pow (Nat.modulo x0 x2) x1) x2.
Definition term110 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.modulo (Nat.mul x0 (Nat.pow x0 x1)) x2).
Definition term103 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.modulo (Nat.mul x0 (Nat.modulo (Nat.pow x0 x1) x2)) x2).
Definition term102 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.modulo (Nat.mul x0 (Nat.modulo (Nat.pow (Nat.modulo x0 x2) x1) x2)) x2).
Definition term93 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.modulo (Nat.mul x0 (Nat.pow (Nat.modulo x0 x2) x1)) x2).
Definition term81 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.modulo (Nat.mul (Nat.modulo x0 x2) (Nat.pow (Nat.modulo x0 x2) x1)) x2).
Definition term80 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.modulo (Nat.pow (Nat.modulo x0 x2) (S x1)) x2).
Definition term50 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (Nat.modulo (Nat.pow (Nat.modulo x0 x1) y0) x1) = (Nat.modulo (Nat.pow x0 y0) x1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.modulo (Nat.pow (Nat.modulo x0 x1) y1) x1) = (Nat.modulo (Nat.pow x0 y1) x1)) y0) -> (fun y1 : nat => (Nat.modulo (Nat.pow (Nat.modulo x0 x1) y1) x1) = (Nat.modulo (Nat.pow x0 y1) x1)) (S y0)).
Definition term34 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.pow (Nat.modulo x0 x1) (NUMERAL 0)) x1.
Definition term4 (a0 : Type') (x0 : a0) (x1 : a0) := forall y0 : a0, ((x1 = x0) /\ (x0 = y0)) -> x1 = y0.
Definition term1 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, forall y2 : a0, ((y0 = y1) /\ (y1 = y2)) -> y0 = y2) x0.
Definition term97 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.modulo (Nat.pow x0 x1) x2).
Definition term96 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul x0 (Nat.modulo (Nat.pow (Nat.modulo x0 x2) x1) x2).
Definition term19 (x0 : nat) := (fun y0 : nat => (Nat.modulo y0 (NUMERAL 0)) = y0) x0.
Definition term84 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.mul x0 (Nat.pow x0 x1)) x2.
Definition term68 (x0 : nat) := Nat.modulo (Nat.pow x0 (NUMERAL 0)).
Definition term73 (x0 : nat) (x1 : nat) := Nat.pow x0 (S x1).
Definition term108 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.modulo (Nat.mul x0 (Nat.modulo y0 x1)) x1) = (Nat.modulo (Nat.mul x0 y0) x1)) x2.
Definition term89 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.modulo (Nat.mul (Nat.modulo x0 x1) y0) x1) = (Nat.modulo (Nat.mul x0 y0) x1)) x2.
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.modulo (Nat.pow (Nat.modulo x0 x1) y0) x1) = (Nat.modulo (Nat.pow x0 y0) x1)) x2.
Definition term109 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.mul x0 (Nat.modulo x1 x2)) x2.
Definition term31 (x0 : nat) (x1 : nat) := (((fun y0 : nat => (Nat.modulo (Nat.pow (Nat.modulo x0 x1) y0) x1) = (Nat.modulo (Nat.pow x0 y0) x1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.modulo (Nat.pow (Nat.modulo x0 x1) y1) x1) = (Nat.modulo (Nat.pow x0 y1) x1)) y0) -> (fun y1 : nat => (Nat.modulo (Nat.pow (Nat.modulo x0 x1) y1) x1) = (Nat.modulo (Nat.pow x0 y1) x1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => (Nat.modulo (Nat.pow (Nat.modulo x0 x1) y1) x1) = (Nat.modulo (Nat.pow x0 y1) x1)) y0.
Definition term77 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.pow (Nat.modulo x0 x1) (S x2)).
Definition term72 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.pow x0 (S y0)) = (Nat.mul x0 (Nat.pow x0 y0))) x1.
Definition term79 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.mul (Nat.modulo x0 x2) (Nat.pow (Nat.modulo x0 x2) x1)) x2.
Definition term60 (x0 : nat) := Nat.pow x0 (NUMERAL 0).
Definition term30 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term15 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0, (exists y2 : a0, (y0 = y2) /\ (y2 = y1)) -> y0 = y1) x0.
Definition term35 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.pow x0 (NUMERAL 0)) x1.
Definition term52 (x0 : nat) (x1 : nat) := imp (((fun y0 : nat => (Nat.modulo (Nat.pow (Nat.modulo x0 x1) y0) x1) = (Nat.modulo (Nat.pow x0 y0) x1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.modulo (Nat.pow (Nat.modulo x0 x1) y1) x1) = (Nat.modulo (Nat.pow x0 y1) x1)) y0) -> (fun y1 : nat => (Nat.modulo (Nat.pow (Nat.modulo x0 x1) y1) x1) = (Nat.modulo (Nat.pow x0 y1) x1)) (S y0))).
Definition term65 (x0 : nat) := Nat.modulo (NUMERAL (BIT1 0)) x0.
Definition term5 (a0 : Type') (x0 : a0) (x1 : a0) (x2 : a0) := (fun y0 : a0 => ((x1 = x0) /\ (x0 = y0)) -> x1 = y0) x2.
Definition term10 (a0 : Type') (x0 : a0) (x1 : a0) := fun y0 : a0 => (x0 = y0) /\ (y0 = x1).
Definition term106 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.modulo (Nat.mul x0 (Nat.modulo y1 y0)) y0) = (Nat.modulo (Nat.mul x0 y1) y0)) x1.
Definition term87 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.modulo (Nat.mul (Nat.modulo x0 y0) y1) y0) = (Nat.modulo (Nat.mul x0 y1) y0)) x1.
Definition term32 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.modulo (Nat.pow (Nat.modulo x0 x1) y0) x1) = (Nat.modulo (Nat.pow x0 y0) x1).
Definition term48 (x0 : nat) (x1 : nat) := forall y0 : nat, ((fun y1 : nat => (Nat.modulo (Nat.pow (Nat.modulo x0 x1) y1) x1) = (Nat.modulo (Nat.pow x0 y1) x1)) y0) -> (fun y1 : nat => (Nat.modulo (Nat.pow (Nat.modulo x0 x1) y1) x1) = (Nat.modulo (Nat.pow x0 y1) x1)) (S y0).
Definition term41 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.modulo (Nat.pow (Nat.modulo x0 x1) y0) x1) = (Nat.modulo (Nat.pow x0 y0) x1)) (S x2).
Definition term114 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term36 (x0 : nat) (x1 : nat) := and ((fun y0 : nat => (Nat.modulo (Nat.pow (Nat.modulo x0 x1) y0) x1) = (Nat.modulo (Nat.pow x0 y0) x1)) (NUMERAL 0)).
Definition term51 (x0 : nat) (x1 : nat) := ((Nat.modulo (Nat.pow (Nat.modulo x0 x1) (NUMERAL 0)) x1) = (Nat.modulo (Nat.pow x0 (NUMERAL 0)) x1)) /\ (forall y0 : nat, ((Nat.modulo (Nat.pow (Nat.modulo x0 x1) y0) x1) = (Nat.modulo (Nat.pow x0 y0) x1)) -> (Nat.modulo (Nat.pow (Nat.modulo x0 x1) (S y0)) x1) = (Nat.modulo (Nat.pow x0 (S y0)) x1)).
Definition term12 (a0 : Type') (x0 : a0) := forall y0 : a0, (exists y1 : a0, (x0 = y1) /\ (y1 = y0)) -> x0 = y0.
Definition term90 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.mul (Nat.modulo x0 x2) x1) x2.
Definition term83 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.mul x0 (Nat.pow x0 x1)).
Definition term16 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => (exists y1 : a0, (x0 = y1) /\ (y1 = y0)) -> x0 = y0) x1.
Definition term59 (x0 : nat) := (fun y0 : nat => (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0))) x0.
Definition term46 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (Nat.modulo (Nat.pow (Nat.modulo x0 x1) y1) x1) = (Nat.modulo (Nat.pow x0 y1) x1)) y0) -> (fun y1 : nat => (Nat.modulo (Nat.pow (Nat.modulo x0 x1) y1) x1) = (Nat.modulo (Nat.pow x0 y1) x1)) (S y0).
Definition term3 (a0 : Type') (x0 : a0) (x1 : a0) := (fun y0 : a0 => forall y1 : a0, ((x0 = y0) /\ (y0 = y1)) -> x0 = y1) x1.
Definition term9 (a0 : Type') (x0 : a0) (x1 : a0) := exists y0 : a0, (x0 = y0) /\ (y0 = x1).
Definition term116 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.pow (Nat.modulo y0 y1) y2) y1) = (Nat.modulo (Nat.pow y0 y2) y1).
Definition term115 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.modulo (Nat.pow (Nat.modulo x0 y0) y1) y0) = (Nat.modulo (Nat.pow x0 y1) y0).
Definition term105 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.modulo (Nat.mul x0 (Nat.modulo y1 y0)) y0) = (Nat.modulo (Nat.mul x0 y1) y0).
Definition term86 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.modulo (Nat.mul (Nat.modulo x0 y0) y1) y0) = (Nat.modulo (Nat.mul x0 y1) y0).
Definition term69 := forall y0 : nat, forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1)).
Definition term18 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term11 (a0 : Type') (x0 : a0) (x1 : a0) := (exists y0 : a0, (x0 = y0) /\ (y0 = x1)) -> x0 = x1.
Definition term67 (x0 : nat) := @eq nat (Nat.modulo (NUMERAL (BIT1 0)) x0).
Definition term112 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, ((Nat.modulo (Nat.mul x0 (Nat.pow (Nat.modulo x0 x2) x1)) x2) = y0) /\ (y0 = (Nat.modulo (Nat.mul x0 (Nat.pow x0 x1)) x2)).
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.pow (Nat.modulo x0 x2) (S x1)) x2.
Definition term0 (a0 : Type') := forall y0 : a0, forall y1 : a0, forall y2 : a0, ((y0 = y1) /\ (y1 = y2)) -> y0 = y2.
Definition term74 (x0 : nat) (x1 : nat) := Nat.mul x0 (Nat.pow x0 x1).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.pow x0 x1) x2.
Definition term45 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.modulo (Nat.pow (Nat.modulo x0 x2) x1) x2) = (Nat.modulo (Nat.pow x0 x1) x2)) -> (Nat.modulo (Nat.pow (Nat.modulo x0 x2) (S x1)) x2) = (Nat.modulo (Nat.pow x0 (S x1)) x2).
Definition term75 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow (Nat.modulo x0 x1) (S x2).
Definition term57 (x0 : nat) (x1 : nat) := (((Nat.modulo (Nat.pow (Nat.modulo x0 x1) (NUMERAL 0)) x1) = (Nat.modulo (Nat.pow x0 (NUMERAL 0)) x1)) /\ (forall y0 : nat, ((Nat.modulo (Nat.pow (Nat.modulo x0 x1) y0) x1) = (Nat.modulo (Nat.pow x0 y0) x1)) -> (Nat.modulo (Nat.pow (Nat.modulo x0 x1) (S y0)) x1) = (Nat.modulo (Nat.pow x0 (S y0)) x1))) -> forall y0 : nat, (Nat.modulo (Nat.pow (Nat.modulo x0 x1) y0) x1) = (Nat.modulo (Nat.pow x0 y0) x1).
Definition term62 (x0 : nat) (x1 : nat) := Nat.pow (Nat.modulo x0 x1) (NUMERAL 0).
Definition term111 (x0 : nat) (x1 : nat) (x2 : nat) := ((Nat.modulo (Nat.mul x0 (Nat.pow (Nat.modulo x0 x2) x1)) x2) = (Nat.modulo (Nat.mul x0 (Nat.modulo (Nat.pow (Nat.modulo x0 x2) x1) x2)) x2)) /\ ((Nat.modulo (Nat.mul x0 (Nat.modulo (Nat.pow (Nat.modulo x0 x2) x1) x2)) x2) = (Nat.modulo (Nat.mul x0 (Nat.pow x0 x1)) x2)).
Definition term53 (x0 : nat) (x1 : nat) := imp (((Nat.modulo (Nat.pow (Nat.modulo x0 x1) (NUMERAL 0)) x1) = (Nat.modulo (Nat.pow x0 (NUMERAL 0)) x1)) /\ (forall y0 : nat, ((Nat.modulo (Nat.pow (Nat.modulo x0 x1) y0) x1) = (Nat.modulo (Nat.pow x0 y0) x1)) -> (Nat.modulo (Nat.pow (Nat.modulo x0 x1) (S y0)) x1) = (Nat.modulo (Nat.pow x0 (S y0)) x1))).
Definition term8 (a0 : Type') (x0 : a0) (x1 : a0) := (forall y0 : a0, forall y1 : a0, forall y2 : a0, ((y0 = y1) /\ (y1 = y2)) -> y0 = y2) -> x0 = x1.
Definition term94 (x0 : nat) (x1 : nat) := (exists y0 : nat, (x0 = y0) /\ (y0 = x1)) -> x0 = x1.
Definition term26 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.pow x0 x1) (NUMERAL 0).
Definition term28 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow x0 x1).
Definition term95 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, ((Nat.modulo (Nat.mul x0 (Nat.pow (Nat.modulo x0 x2) x1)) x2) = y0) /\ (y0 = (Nat.modulo (Nat.mul x0 (Nat.pow x0 x1)) x2))) -> (Nat.modulo (Nat.mul x0 (Nat.pow (Nat.modulo x0 x2) x1)) x2) = (Nat.modulo (Nat.mul x0 (Nat.pow x0 x1)) x2).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.modulo (Nat.pow (Nat.modulo x0 x2) x1) x2).
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((Nat.modulo (Nat.pow (Nat.modulo x0 x2) x1) x2) = (Nat.modulo (Nat.pow x0 x1) x2)).
Definition term70 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.pow y0 (S y1)) = (Nat.mul y0 (Nat.pow y0 y1))) x0.
Definition term58 := forall y0 : nat, (Nat.pow y0 (NUMERAL 0)) = (NUMERAL (BIT1 0)).
Definition term49 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.modulo (Nat.pow (Nat.modulo x0 x1) y0) x1) = (Nat.modulo (Nat.pow x0 y0) x1)) -> (Nat.modulo (Nat.pow (Nat.modulo x0 x1) (S y0)) x1) = (Nat.modulo (Nat.pow x0 (S y0)) x1).
Definition term13 (a0 : Type') := forall y0 : a0, forall y1 : a0, (exists y2 : a0, (y0 = y2) /\ (y2 = y1)) -> y0 = y1.
Definition term2 (a0 : Type') (x0 : a0) := forall y0 : a0, forall y1 : a0, ((x0 = y0) /\ (y0 = y1)) -> x0 = y1.
Definition term78 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.mul (Nat.modulo x0 x1) (Nat.pow (Nat.modulo x0 x1) x2)).
Definition term82 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.pow x0 (S x1)).
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.pow (Nat.modulo x0 x1) x2).
Definition term76 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.mul (Nat.modulo x0 x1) (Nat.pow (Nat.modulo x0 x1) x2).
Definition term54 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (Nat.modulo (Nat.pow (Nat.modulo x0 x1) y1) x1) = (Nat.modulo (Nat.pow x0 y1) x1)) y0.
Definition term113 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => ((Nat.modulo (Nat.mul x0 (Nat.pow (Nat.modulo x0 x2) x1)) x2) = y0) /\ (y0 = (Nat.modulo (Nat.mul x0 (Nat.pow x0 x1)) x2)).
Definition term63 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.pow (Nat.modulo x0 x1) (NUMERAL 0)).
Definition term99 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.mul x0 (Nat.modulo (Nat.pow x0 x1) x2)).
Definition term98 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.mul x0 (Nat.modulo (Nat.pow (Nat.modulo x0 x2) x1) x2)).
Definition term47 (x0 : nat) (x1 : nat) := fun y0 : nat => ((Nat.modulo (Nat.pow (Nat.modulo x0 x1) y0) x1) = (Nat.modulo (Nat.pow x0 y0) x1)) -> (Nat.modulo (Nat.pow (Nat.modulo x0 x1) (S y0)) x1) = (Nat.modulo (Nat.pow x0 (S y0)) x1).
Definition term44 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => (Nat.modulo (Nat.pow (Nat.modulo x0 x1) y0) x1) = (Nat.modulo (Nat.pow x0 y0) x1)) x2) -> (fun y0 : nat => (Nat.modulo (Nat.pow (Nat.modulo x0 x1) y0) x1) = (Nat.modulo (Nat.pow x0 y0) x1)) (S x2).
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((fun y0 : nat => (Nat.modulo (Nat.pow (Nat.modulo x0 x1) y0) x1) = (Nat.modulo (Nat.pow x0 y0) x1)) x2).
Definition term43 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.pow x0 (S x1)) x2.
Definition term107 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.modulo (Nat.mul x0 (Nat.modulo y0 x1)) x1) = (Nat.modulo (Nat.mul x0 y0) x1).
Definition term88 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.modulo (Nat.mul (Nat.modulo x0 x1) y0) x1) = (Nat.modulo (Nat.mul x0 y0) x1).
Definition term56 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.modulo (Nat.pow (Nat.modulo x0 x1) y0) x1) = (Nat.modulo (Nat.pow x0 y0) x1).
Definition term66 (x0 : nat) (x1 : nat) := @eq nat (Nat.modulo (Nat.pow (Nat.modulo x0 x1) (NUMERAL 0)) x1).
Definition term33 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.modulo (Nat.pow (Nat.modulo x0 x1) y0) x1) = (Nat.modulo (Nat.pow x0 y0) x1)) (NUMERAL 0).
Definition term17 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term61 := NUMERAL (BIT1 0).
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.pow (Nat.modulo x0 x1) x2.
