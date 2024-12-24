Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term91 (x0 : real) := @eq real (real_mul (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term29 (x0 : real) := @eq real (real_mul (real_of_num (NUMERAL 0)) x0).
Definition term13 (x0 : real) (x1 : real) (x2 : real) := real_mul x0 (real_mul x1 x2).
Definition term75 := (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) /\ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) /\ ((forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) /\ (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0))).
Definition term17 := real_of_num (NUMERAL 0).
Definition term79 := and (forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)).
Definition term76 := and (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)).
Definition term70 := and (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)).
Definition term67 := and (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)).
Definition term44 := and (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))).
Definition term51 := and (forall y0 : real, (real_pow y0 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term37 := and (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))).
Definition term35 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term33 := forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0)).
Definition term47 (x0 : real) := @eq real (real_pow x0 (NUMERAL 0)).
Definition term92 := fun y0 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0.
Definition term58 := fun y0 : real => forall y1 : nat, (real_pow y0 (S y1)) = (real_mul y0 (real_pow y0 y1)).
Definition term74 := (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) /\ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) /\ ((forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) /\ ((forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) /\ ((forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) /\ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))) /\ ((forall y0 : real, (real_pow y0 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y0 : real, forall y1 : nat, (real_pow y0 (S y1)) = (real_mul y0 (real_pow y0 y1))))))))).
Definition term64 := (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) /\ ((forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) /\ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))) /\ ((forall y0 : real, (real_pow y0 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y0 : real, forall y1 : nat, (real_pow y0 (S y1)) = (real_mul y0 (real_pow y0 y1)))))).
Definition term25 (x0 : real) := forall y0 : nat, (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0)).
Definition term32 := fun y0 : real => True.
Definition term109 (x0 : real) := forall y0 : real, (real_add x0 y0) = (real_add y0 x0).
Definition term1 (x0 : real) := forall y0 : real, (real_mul x0 y0) = (real_mul y0 x0).
Definition term28 (x0 : real) (x1 : nat) := real_mul x0 (real_pow x0 x1).
Definition term50 := forall y0 : real, (real_pow y0 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0))).
Definition term96 := (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) /\ (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)).
Definition term2 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul x0 y0) = (real_mul y0 x0)) x1.
Definition term27 (x0 : real) (x1 : nat) := real_pow x0 (S x1).
Definition term26 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0))) x1.
Definition term108 (x0 : real) := fun y0 : real => (real_add x0 y0) = (real_add y0 x0).
Definition term34 := forall y0 : real, True.
Definition term36 (x0 : Prop) := forall y0 : real, x0.
Definition term65 := (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) /\ True.
Definition term45 (x0 : real) := real_pow x0 (NUMERAL 0).
Definition term73 := and (forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0).
Definition term63 := and (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0).
Definition term111 := forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0).
Definition term106 := forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2).
Definition term104 (x0 : real) := forall y0 : real, forall y1 : real, (real_add x0 (real_add y0 y1)) = (real_add (real_add x0 y0) y1).
Definition term94 := forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0).
Definition term90 := forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2).
Definition term59 := forall y0 : real, forall y1 : nat, (real_pow y0 (S y1)) = (real_mul y0 (real_pow y0 y1)).
Definition term43 := forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2)).
Definition term19 (x0 : real) := forall y0 : real, forall y1 : real, (real_mul x0 (real_add y0 y1)) = (real_add (real_mul x0 y0) (real_mul x0 y1)).
Definition term9 (x0 : real) := forall y0 : real, forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1).
Definition term95 := True /\ (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)).
Definition term54 (x0 : real) := fun y0 : nat => (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0)).
Definition term12 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0)) x2.
Definition term21 (x0 : real) (x1 : real) := forall y0 : real, (real_mul x1 (real_add x0 y0)) = (real_add (real_mul x1 x0) (real_mul x1 y0)).
Definition term6 (x0 : real) := (fun y0 : real => (real_add (real_of_num (NUMERAL 0)) y0) = y0) x0.
Definition term4 (x0 : real) := (fun y0 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) x0.
Definition term97 := (forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) /\ ((forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) /\ (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0))).
Definition term72 := (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) /\ ((forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) /\ (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0)).
Definition term61 := (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))) /\ ((forall y0 : real, (real_pow y0 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y0 : real, forall y1 : nat, (real_pow y0 (S y1)) = (real_mul y0 (real_pow y0 y1)))).
Definition term81 := (forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) /\ ((forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) /\ ((forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) /\ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) /\ ((forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) /\ (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0))))).
Definition term80 := (forall y0 : real, forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2)) /\ ((forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) /\ ((forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) /\ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) /\ ((forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) /\ ((forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) /\ ((forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) /\ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))) /\ ((forall y0 : real, (real_pow y0 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y0 : real, forall y1 : nat, (real_pow y0 (S y1)) = (real_mul y0 (real_pow y0 y1))))))))))).
Definition term77 := (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) /\ ((forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) /\ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) /\ ((forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) /\ ((forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) /\ ((forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) /\ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))) /\ ((forall y0 : real, (real_pow y0 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y0 : real, forall y1 : nat, (real_pow y0 (S y1)) = (real_mul y0 (real_pow y0 y1)))))))))).
Definition term71 := (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) /\ ((forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) /\ ((forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) /\ ((forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) /\ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))) /\ ((forall y0 : real, (real_pow y0 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y0 : real, forall y1 : nat, (real_pow y0 (S y1)) = (real_mul y0 (real_pow y0 y1)))))))).
Definition term68 := (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) /\ ((forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) /\ ((forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) /\ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))) /\ ((forall y0 : real, (real_pow y0 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y0 : real, forall y1 : nat, (real_pow y0 (S y1)) = (real_mul y0 (real_pow y0 y1))))))).
Definition term41 (x0 : real) := fun y0 : real => forall y1 : real, (real_mul x0 (real_add y0 y1)) = (real_add (real_mul x0 y0) (real_mul x0 y1)).
Definition term100 (x0 : real) (x1 : real) (x2 : real) := @eq real (real_add x0 (real_add x1 x2)).
Definition term101 (x0 : real) (x1 : real) := fun y0 : real => (real_add x0 (real_add x1 y0)) = (real_add (real_add x0 x1) y0).
Definition term3 (x0 : real) (x1 : real) (x2 : real) := ((real_add (real_add x1 x0) x2) = (real_add x1 (real_add x0 x2))) /\ ((real_add x1 (real_add x0 x2)) = (real_add x0 (real_add x1 x2))).
Definition term102 (x0 : real) (x1 : real) := forall y0 : real, (real_add x0 (real_add x1 y0)) = (real_add (real_add x0 x1) y0).
Definition term11 (x0 : real) (x1 : real) := forall y0 : real, (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0).
Definition term30 := @eq real (real_of_num (NUMERAL 0)).
Definition term5 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term84 := forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0.
Definition term66 := forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0.
Definition term49 := fun y0 : real => (real_pow y0 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0))).
Definition term56 := forall y0 : nat, True.
Definition term31 := fun y0 : real => (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0)).
Definition term114 := fun y0 : real => forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0).
Definition term110 := fun y0 : real => forall y1 : real, (real_add y0 y1) = (real_add y1 y0).
Definition term103 (x0 : real) := fun y0 : real => forall y1 : real, (real_add x0 (real_add y0 y1)) = (real_add (real_add x0 y0) y1).
Definition term88 (x0 : real) := fun y0 : real => forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1).
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) x0.
Definition term60 := (forall y0 : real, (real_pow y0 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y0 : real, forall y1 : nat, (real_pow y0 (S y1)) = (real_mul y0 (real_pow y0 y1))).
Definition term55 := fun y0 : nat => True.
Definition term24 (x0 : real) (x1 : real) (x2 : real) := real_add (real_mul x1 x0) (real_mul x1 x2).
Definition term15 (x0 : real) := (fun y0 : real => (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) x0.
Definition term23 (x0 : real) (x1 : real) (x2 : real) := real_mul x0 (real_add x1 x2).
Definition term52 (x0 : real) (x1 : nat) := @eq real (real_pow x0 (S x1)).
Definition term20 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_mul x0 (real_add y0 y1)) = (real_add (real_mul x0 y0) (real_mul x0 y1))) x1.
Definition term10 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1)) x1.
Definition term99 (x0 : real) (x1 : real) (x2 : real) := real_add x0 (real_add x1 x2).
Definition term78 := (forall y0 : real, forall y1 : real, (real_add y0 y1) = (real_add y1 y0)) /\ ((forall y0 : real, (real_add (real_of_num (NUMERAL 0)) y0) = y0) /\ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) /\ ((forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) /\ (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0)))).
Definition term82 (x0 : real) := @eq real (real_add (real_of_num (NUMERAL 0)) x0).
Definition term113 (x0 : real) := fun y0 : real => (real_mul x0 y0) = (real_mul y0 x0).
Definition term105 := fun y0 : real => forall y1 : real, forall y2 : real, (real_add y0 (real_add y1 y2)) = (real_add (real_add y0 y1) y2).
Definition term89 := fun y0 : real => forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2).
Definition term42 := fun y0 : real => forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2)).
Definition term62 := (forall y0 : real, (real_mul (real_of_num (NUMERAL 0)) y0) = (real_of_num (NUMERAL 0))) /\ ((forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))) /\ ((forall y0 : real, (real_pow y0 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y0 : real, forall y1 : nat, (real_pow y0 (S y1)) = (real_mul y0 (real_pow y0 y1))))).
Definition term112 (x0 : real) (x1 : real) := @eq real (real_mul x0 x1).
Definition term69 := (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) /\ (forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0).
Definition term93 := (forall y0 : real, forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) /\ True.
Definition term39 (x0 : real) (x1 : real) (x2 : real) := @eq real (real_add (real_mul x1 x0) (real_mul x1 x2)).
Definition term7 (x0 : real) := real_add (real_of_num (NUMERAL 0)) x0.
Definition term46 := real_of_num (NUMERAL (BIT1 0)).
Definition term14 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_mul x0 x1) x2.
Definition term107 (x0 : real) (x1 : real) := @eq real (real_add x0 x1).
Definition term16 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term22 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_mul x1 (real_add x0 y0)) = (real_add (real_mul x1 x0) (real_mul x1 y0))) x2.
Definition term57 (x0 : Prop) := forall y0 : nat, x0.
Definition term87 (x0 : real) (x1 : real) := fun y0 : real => (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0).
Definition term48 := @eq real (real_of_num (NUMERAL (BIT1 0))).
Definition term53 (x0 : real) (x1 : nat) := @eq real (real_mul x0 (real_pow x0 x1)).
Definition term85 (x0 : real) (x1 : real) (x2 : real) := @eq real (real_mul x0 (real_mul x1 x2)).
Definition term38 (x0 : real) (x1 : real) (x2 : real) := @eq real (real_mul x0 (real_add x1 x2)).
Definition term98 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add x0 x1) x2.
Definition term86 (x0 : real) (x1 : real) (x2 : real) := @eq real (real_mul (real_mul x0 x1) x2).
Definition term40 (x0 : real) (x1 : real) := fun y0 : real => (real_mul x1 (real_add x0 y0)) = (real_add (real_mul x1 x0) (real_mul x1 y0)).
Definition term18 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_mul y0 (real_add y1 y2)) = (real_add (real_mul y0 y1) (real_mul y0 y2))) x0.
Definition term8 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) x0.
Definition term83 := fun y0 : real => (real_add (real_of_num (NUMERAL 0)) y0) = y0.
