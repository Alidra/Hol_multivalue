Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : int) (x1 : int) (x2 : int) := rem (int_mul (rem x0 x2) (rem x1 x2)) x2.
Definition term22 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, (rem (int_mul x0 y0) y1) = (rem (int_mul (rem x0 y1) (rem y0 y1)) y1)) x1.
Definition term2 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, (rem (int_mul (rem x0 y1) (rem y0 y1)) y1) = (rem (int_mul x0 y0) y1)) x1.
Definition term82 (x0 : int) (x1 : nat) (x2 : int) := rem (int_mul x0 (int_pow x0 x1)) x2.
Definition term18 := fun y0 : int => forall y1 : int, forall y2 : int, (rem (int_mul y0 y1) y2) = (rem (int_mul (rem y0 y2) (rem y1 y2)) y2).
Definition term17 := fun y0 : int => forall y1 : int, forall y2 : int, (rem (int_mul (rem y0 y2) (rem y1 y2)) y2) = (rem (int_mul y0 y1) y2).
Definition term6 (x0 : int) (x1 : int) (x2 : int) := rem (int_mul x0 x1) x2.
Definition term80 (x0 : int) (x1 : nat) := rem (int_mul x0 (int_pow x0 x1)).
Definition term69 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term67 := fun y0 : int => True.
Definition term7 (x0 : int) := (fun y0 : int => forall y1 : int, (rem (rem y0 y1) y1) = (rem y0 y1)) x0.
Definition term46 (x0 : int) := forall y0 : nat, (forall y1 : int, (rem (int_pow (rem x0 y1) y0) y1) = (rem (int_pow x0 y0) y1)) -> forall y1 : int, (rem (int_pow (rem x0 y1) (S y0)) y1) = (rem (int_pow x0 (S y0)) y1).
Definition term62 (x0 : int) (x1 : int) := @eq int (rem (int_pow (rem x0 x1) (NUMERAL 0)) x1).
Definition term24 (x0 : int) := forall y0 : nat, (int_pow x0 (S y0)) = (int_mul x0 (int_pow x0 y0)).
Definition term63 (x0 : int) := @eq int (rem (int_of_num (NUMERAL (BIT1 0))) x0).
Definition term10 (x0 : int) (x1 : int) := rem (rem x0 x1) x1.
Definition term39 (x0 : int) (x1 : nat) := (fun y0 : nat => forall y1 : int, (rem (int_pow (rem x0 y1) y0) y1) = (rem (int_pow x0 y0) y1)) (S x1).
Definition term21 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (rem (int_mul y0 y1) y2) = (rem (int_mul (rem y0 y2) (rem y1 y2)) y2)) x0.
Definition term0 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (rem (int_mul (rem y0 y2) (rem y1 y2)) y2) = (rem (int_mul y0 y1) y2)) x0.
Definition term54 (x0 : int) := ((forall y0 : int, (rem (int_pow (rem x0 y0) (NUMERAL 0)) y0) = (rem (int_pow x0 (NUMERAL 0)) y0)) /\ (forall y0 : nat, (forall y1 : int, (rem (int_pow (rem x0 y1) y0) y1) = (rem (int_pow x0 y0) y1)) -> forall y1 : int, (rem (int_pow (rem x0 y1) (S y0)) y1) = (rem (int_pow x0 (S y0)) y1))) -> forall y0 : nat, forall y1 : int, (rem (int_pow (rem x0 y1) y0) y1) = (rem (int_pow x0 y0) y1).
Definition term102 (x0 : int) (x1 : nat) (x2 : int) := rem (int_mul (rem x0 x2) (rem (int_pow x0 x1) x2)) x2.
Definition term97 (x0 : int) (x1 : nat) (x2 : int) := rem (int_mul (rem (rem x0 x2) x2) (rem (int_pow x0 x1) x2)) x2.
Definition term86 (x0 : int) (x1 : nat) (x2 : int) := rem (int_mul (rem (rem x0 x2) x2) (rem (int_pow (rem x0 x2) x1) x2)) x2.
Definition term57 (x0 : int) (x1 : int) := int_pow (rem x0 x1) (NUMERAL 0).
Definition term79 (x0 : int) (x1 : nat) := rem (int_pow x0 (S x1)).
Definition term91 (x0 : int) (x1 : nat) (x2 : int) := rem (int_pow x0 x1) x2.
Definition term96 (x0 : int) (x1 : nat) (x2 : int) := rem (int_mul (rem (rem x0 x2) x2) (rem (int_pow x0 x1) x2)).
Definition term95 (x0 : int) (x1 : nat) (x2 : int) := rem (int_mul (rem (rem x0 x2) x2) (rem (int_pow (rem x0 x2) x1) x2)).
Definition term101 (x0 : int) (x1 : nat) (x2 : int) := rem (int_mul (rem x0 x2) (rem (int_pow x0 x1) x2)).
Definition term29 (x0 : int) := (((fun y0 : nat => forall y1 : int, (rem (int_pow (rem x0 y1) y0) y1) = (rem (int_pow x0 y0) y1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : int, (rem (int_pow (rem x0 y2) y1) y2) = (rem (int_pow x0 y1) y2)) y0) -> (fun y1 : nat => forall y2 : int, (rem (int_pow (rem x0 y2) y1) y2) = (rem (int_pow x0 y1) y2)) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : int, (rem (int_pow (rem x0 y2) y1) y2) = (rem (int_pow x0 y1) y2)) y0.
Definition term58 (x0 : int) (x1 : int) := rem (int_pow (rem x0 x1) (NUMERAL 0)).
Definition term28 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term49 (x0 : int) := imp (((fun y0 : nat => forall y1 : int, (rem (int_pow (rem x0 y1) y0) y1) = (rem (int_pow x0 y0) y1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : int, (rem (int_pow (rem x0 y2) y1) y2) = (rem (int_pow x0 y1) y2)) y0) -> (fun y1 : nat => forall y2 : int, (rem (int_pow (rem x0 y2) y1) y2) = (rem (int_pow x0 y1) y2)) (S y0))).
Definition term27 (x0 : int) (x1 : nat) := int_mul x0 (int_pow x0 x1).
Definition term45 (x0 : int) := forall y0 : nat, ((fun y1 : nat => forall y2 : int, (rem (int_pow (rem x0 y2) y1) y2) = (rem (int_pow x0 y1) y2)) y0) -> (fun y1 : nat => forall y2 : int, (rem (int_pow (rem x0 y2) y1) y2) = (rem (int_pow x0 y1) y2)) (S y0).
Definition term74 (x0 : int) (x1 : int) (x2 : nat) := rem (int_mul (rem x0 x1) (int_pow (rem x0 x1) x2)).
Definition term75 (x0 : int) (x1 : nat) (x2 : int) := rem (int_pow (rem x0 x2) (S x1)) x2.
Definition term35 (x0 : int) (x1 : nat) := (fun y0 : nat => forall y1 : int, (rem (int_pow (rem x0 y1) y0) y1) = (rem (int_pow x0 y0) y1)) x1.
Definition term64 (x0 : int) := rem (int_pow x0 (NUMERAL 0)).
Definition term9 (x0 : int) (x1 : int) := (fun y0 : int => (rem (rem x0 y0) y0) = (rem x0 y0)) x1.
Definition term33 (x0 : int) := and ((fun y0 : nat => forall y1 : int, (rem (int_pow (rem x0 y1) y0) y1) = (rem (int_pow x0 y0) y1)) (NUMERAL 0)).
Definition term73 (x0 : int) (x1 : int) (x2 : nat) := rem (int_pow (rem x0 x1) (S x2)).
Definition term31 (x0 : int) := (fun y0 : nat => forall y1 : int, (rem (int_pow (rem x0 y1) y0) y1) = (rem (int_pow x0 y0) y1)) (NUMERAL 0).
Definition term50 (x0 : int) := imp ((forall y0 : int, (rem (int_pow (rem x0 y0) (NUMERAL 0)) y0) = (rem (int_pow x0 (NUMERAL 0)) y0)) /\ (forall y0 : nat, (forall y1 : int, (rem (int_pow (rem x0 y1) y0) y1) = (rem (int_pow x0 y0) y1)) -> forall y1 : int, (rem (int_pow (rem x0 y1) (S y0)) y1) = (rem (int_pow x0 (S y0)) y1))).
Definition term85 (x0 : int) (x1 : nat) := forall y0 : int, (rem (int_mul (rem x0 y0) (int_pow (rem x0 y0) x1)) y0) = (rem (int_mul x0 (int_pow x0 x1)) y0).
Definition term40 (x0 : int) (x1 : nat) := forall y0 : int, (rem (int_pow (rem x0 y0) (S x1)) y0) = (rem (int_pow x0 (S x1)) y0).
Definition term36 (x0 : int) (x1 : nat) := forall y0 : int, (rem (int_pow (rem x0 y0) x1) y0) = (rem (int_pow x0 x1) y0).
Definition term32 (x0 : int) := forall y0 : int, (rem (int_pow (rem x0 y0) (NUMERAL 0)) y0) = (rem (int_pow x0 (NUMERAL 0)) y0).
Definition term13 (x0 : int) (x1 : int) := forall y0 : int, (rem (int_mul x0 x1) y0) = (rem (int_mul (rem x0 y0) (rem x1 y0)) y0).
Definition term3 (x0 : int) (x1 : int) := forall y0 : int, (rem (int_mul (rem x0 y0) (rem x1 y0)) y0) = (rem (int_mul x0 x1) y0).
Definition term53 (x0 : int) := forall y0 : nat, forall y1 : int, (rem (int_pow (rem x0 y1) y0) y1) = (rem (int_pow x0 y0) y1).
Definition term65 (x0 : int) (x1 : int) := rem (int_pow x0 (NUMERAL 0)) x1.
Definition term70 (x0 : Prop) := forall y0 : int, x0.
Definition term55 (x0 : int) := int_pow x0 (NUMERAL 0).
Definition term105 := forall y0 : int, forall y1 : nat, forall y2 : int, (rem (int_pow (rem y0 y2) y1) y2) = (rem (int_pow y0 y1) y2).
Definition term20 := forall y0 : int, forall y1 : int, forall y2 : int, (rem (int_mul y0 y1) y2) = (rem (int_mul (rem y0 y2) (rem y1 y2)) y2).
Definition term19 := forall y0 : int, forall y1 : int, forall y2 : int, (rem (int_mul (rem y0 y2) (rem y1 y2)) y2) = (rem (int_mul y0 y1) y2).
Definition term16 (x0 : int) := forall y0 : int, forall y1 : int, (rem (int_mul x0 y0) y1) = (rem (int_mul (rem x0 y1) (rem y0 y1)) y1).
Definition term1 (x0 : int) := forall y0 : int, forall y1 : int, (rem (int_mul (rem x0 y1) (rem y0 y1)) y1) = (rem (int_mul x0 y0) y1).
Definition term30 (x0 : int) := fun y0 : nat => forall y1 : int, (rem (int_pow (rem x0 y1) y0) y1) = (rem (int_pow x0 y0) y1).
Definition term25 (x0 : int) (x1 : nat) := (fun y0 : nat => (int_pow x0 (S y0)) = (int_mul x0 (int_pow x0 y0))) x1.
Definition term11 (x0 : int) (x1 : int) := fun y0 : int => (rem (int_mul (rem x0 y0) (rem x1 y0)) y0) = (rem (int_mul x0 x1) y0).
Definition term37 (x0 : int) (x1 : nat) := imp ((fun y0 : nat => forall y1 : int, (rem (int_pow (rem x0 y1) y0) y1) = (rem (int_pow x0 y0) y1)) x1).
Definition term42 (x0 : int) (x1 : nat) := (forall y0 : int, (rem (int_pow (rem x0 y0) x1) y0) = (rem (int_pow x0 x1) y0)) -> forall y0 : int, (rem (int_pow (rem x0 y0) (S x1)) y0) = (rem (int_pow x0 (S x1)) y0).
Definition term15 (x0 : int) := fun y0 : int => forall y1 : int, (rem (int_mul x0 y0) y1) = (rem (int_mul (rem x0 y1) (rem y0 y1)) y1).
Definition term14 (x0 : int) := fun y0 : int => forall y1 : int, (rem (int_mul (rem x0 y1) (rem y0 y1)) y1) = (rem (int_mul x0 y0) y1).
Definition term84 (x0 : int) (x1 : nat) := fun y0 : int => (rem (int_mul (rem x0 y0) (int_pow (rem x0 y0) x1)) y0) = (rem (int_mul x0 (int_pow x0 x1)) y0).
Definition term83 (x0 : int) (x1 : nat) := fun y0 : int => (rem (int_pow (rem x0 y0) (S x1)) y0) = (rem (int_pow x0 (S x1)) y0).
Definition term66 (x0 : int) := fun y0 : int => (rem (int_pow (rem x0 y0) (NUMERAL 0)) y0) = (rem (int_pow x0 (NUMERAL 0)) y0).
Definition term12 (x0 : int) (x1 : int) := fun y0 : int => (rem (int_mul x0 x1) y0) = (rem (int_mul (rem x0 y0) (rem x1 y0)) y0).
Definition term26 (x0 : int) (x1 : nat) := int_pow x0 (S x1).
Definition term71 (x0 : int) (x1 : int) (x2 : nat) := int_pow (rem x0 x1) (S x2).
Definition term44 (x0 : int) := fun y0 : nat => (forall y1 : int, (rem (int_pow (rem x0 y1) y0) y1) = (rem (int_pow x0 y0) y1)) -> forall y1 : int, (rem (int_pow (rem x0 y1) (S y0)) y1) = (rem (int_pow x0 (S y0)) y1).
Definition term43 (x0 : int) := fun y0 : nat => ((fun y1 : nat => forall y2 : int, (rem (int_pow (rem x0 y2) y1) y2) = (rem (int_pow x0 y1) y2)) y0) -> (fun y1 : nat => forall y2 : int, (rem (int_pow (rem x0 y2) y1) y2) = (rem (int_pow x0 y1) y2)) (S y0).
Definition term81 (x0 : int) (x1 : nat) (x2 : int) := rem (int_pow x0 (S x1)) x2.
Definition term41 (x0 : int) (x1 : nat) := ((fun y0 : nat => forall y1 : int, (rem (int_pow (rem x0 y1) y0) y1) = (rem (int_pow x0 y0) y1)) x1) -> (fun y0 : nat => forall y1 : int, (rem (int_pow (rem x0 y1) y0) y1) = (rem (int_pow x0 y0) y1)) (S x1).
Definition term60 (x0 : int) (x1 : int) := rem (int_pow (rem x0 x1) (NUMERAL 0)) x1.
Definition term99 (x0 : int) (x1 : int) := int_mul (rem x0 x1).
Definition term72 (x0 : int) (x1 : int) (x2 : nat) := int_mul (rem x0 x1) (int_pow (rem x0 x1) x2).
Definition term48 (x0 : int) := (forall y0 : int, (rem (int_pow (rem x0 y0) (NUMERAL 0)) y0) = (rem (int_pow x0 (NUMERAL 0)) y0)) /\ (forall y0 : nat, (forall y1 : int, (rem (int_pow (rem x0 y1) y0) y1) = (rem (int_pow x0 y0) y1)) -> forall y1 : int, (rem (int_pow (rem x0 y1) (S y0)) y1) = (rem (int_pow x0 (S y0)) y1)).
Definition term100 (x0 : int) (x1 : nat) (x2 : int) := int_mul (rem x0 x2) (rem (int_pow x0 x1) x2).
Definition term68 := forall y0 : int, True.
Definition term94 (x0 : int) (x1 : nat) (x2 : int) := int_mul (rem (rem x0 x2) x2) (rem (int_pow x0 x1) x2).
Definition term93 (x0 : int) (x1 : nat) (x2 : int) := int_mul (rem (rem x0 x2) x2) (rem (int_pow (rem x0 x2) x1) x2).
Definition term76 (x0 : int) (x1 : nat) (x2 : int) := rem (int_mul (rem x0 x2) (int_pow (rem x0 x2) x1)) x2.
Definition term51 (x0 : int) := fun y0 : nat => (fun y1 : nat => forall y2 : int, (rem (int_pow (rem x0 y2) y1) y2) = (rem (int_pow x0 y1) y2)) y0.
Definition term34 (x0 : int) := and (forall y0 : int, (rem (int_pow (rem x0 y0) (NUMERAL 0)) y0) = (rem (int_pow x0 (NUMERAL 0)) y0)).
Definition term90 (x0 : int) (x1 : nat) (x2 : int) := rem (int_pow (rem x0 x2) x1) x2.
Definition term47 (x0 : int) := ((fun y0 : nat => forall y1 : int, (rem (int_pow (rem x0 y1) y0) y1) = (rem (int_pow x0 y0) y1)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : int, (rem (int_pow (rem x0 y2) y1) y2) = (rem (int_pow x0 y1) y2)) y0) -> (fun y1 : nat => forall y2 : int, (rem (int_pow (rem x0 y2) y1) y2) = (rem (int_pow x0 y1) y2)) (S y0)).
Definition term59 := rem (int_of_num (NUMERAL (BIT1 0))).
Definition term104 (x0 : int) (x1 : nat) (x2 : int) := @eq int (rem (int_mul x0 (int_pow x0 x1)) x2).
Definition term103 (x0 : int) (x1 : nat) (x2 : int) := @eq int (rem (int_mul (rem x0 x2) (rem (int_pow x0 x1) x2)) x2).
Definition term98 (x0 : int) (x1 : nat) (x2 : int) := @eq int (rem (int_mul (rem (rem x0 x2) x2) (rem (int_pow x0 x1) x2)) x2).
Definition term88 (x0 : int) (x1 : nat) (x2 : int) := @eq int (rem (int_mul (rem (rem x0 x2) x2) (rem (int_pow (rem x0 x2) x1) x2)) x2).
Definition term78 (x0 : int) (x1 : nat) (x2 : int) := @eq int (rem (int_mul (rem x0 x2) (int_pow (rem x0 x2) x1)) x2).
Definition term77 (x0 : int) (x1 : nat) (x2 : int) := @eq int (rem (int_pow (rem x0 x2) (S x1)) x2).
Definition term92 (x0 : int) (x1 : int) := int_mul (rem (rem x0 x1) x1).
Definition term61 (x0 : int) := rem (int_of_num (NUMERAL (BIT1 0))) x0.
Definition term8 (x0 : int) := forall y0 : int, (rem (rem x0 y0) y0) = (rem x0 y0).
Definition term38 (x0 : int) (x1 : nat) := imp (forall y0 : int, (rem (int_pow (rem x0 y0) x1) y0) = (rem (int_pow x0 x1) y0)).
Definition term52 (x0 : int) := forall y0 : nat, (fun y1 : nat => forall y2 : int, (rem (int_pow (rem x0 y2) y1) y2) = (rem (int_pow x0 y1) y2)) y0.
Definition term89 (x0 : int) (x1 : nat) (x2 : int) := (fun y0 : int => (rem (int_pow (rem x0 y0) x1) y0) = (rem (int_pow x0 x1) y0)) x2.
Definition term23 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (rem (int_mul x0 x1) y0) = (rem (int_mul (rem x0 y0) (rem x1 y0)) y0)) x2.
Definition term4 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (rem (int_mul (rem x0 y0) (rem x1 y0)) y0) = (rem (int_mul x0 x1) y0)) x2.
Definition term56 := int_of_num (NUMERAL (BIT1 0)).
Definition term87 (x0 : int) (x1 : int) (x2 : nat) := int_pow (rem x0 x1) x2.
