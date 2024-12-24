Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term64 (x0 : real) (x1 : real) := real_le (real_pow x0 (NUMERAL 0)) (real_pow x1 (NUMERAL 0)).
Definition term35 := fun y0 : nat => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0).
Definition term43 (x0 : nat) := imp (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_pow y0 x0) (real_pow y1 x0)).
Definition term40 (x0 : nat) := (fun y0 : nat => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) x0.
Definition term65 := real_le (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term39 := and (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_pow y0 (NUMERAL 0)) (real_pow y1 (NUMERAL 0))).
Definition term77 (x0 : real) (x1 : nat) := real_le (real_pow x0 (S x1)).
Definition term67 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 x1)) -> real_le (real_pow x0 (NUMERAL 0)) (real_pow x1 (NUMERAL 0)).
Definition term74 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term84 (x0 : real) (x1 : nat) := fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 y0)) -> real_le (real_mul x0 (real_pow x0 x1)) (real_mul y0 (real_pow y0 x1)).
Definition term51 := forall y0 : nat, (forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 (S y0)) (real_pow y2 (S y0)).
Definition term29 (x0 : real) := forall y0 : nat, (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0)).
Definition term4 (x0 : real) (x1 : nat) := (real_le (real_of_num (NUMERAL 0)) x0) -> real_le (real_of_num (NUMERAL 0)) (real_pow x0 x1).
Definition term71 := fun y0 : real => True.
Definition term103 (x0 : nat) := (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_pow y0 x0) (real_pow y1 x0)) -> forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_pow y0 x0) (real_pow y1 x0).
Definition term47 (x0 : nat) := (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_pow y0 x0) (real_pow y1 x0)) -> forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_pow y0 (S x0)) (real_pow y1 (S x0)).
Definition term24 := (forall y0 : real, forall y1 : real, forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_le y0 y1) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_le y2 y3)))) -> real_le (real_mul y0 y2) (real_mul y1 y3)) -> forall y0 : real, forall y1 : real, forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_le y0 y2) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y3)))) -> real_le (real_mul y0 y1) (real_mul y2 y3).
Definition term8 := (forall y0 : real, forall y1 : nat, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (real_pow y0 y1)) -> forall y0 : real, forall y1 : nat, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (real_pow y0 y1).
Definition term96 (x0 : real) (x1 : real) (x2 : nat) := (real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_le x0 x1) /\ ((real_le (real_of_num (NUMERAL 0)) (real_pow x0 x2)) /\ (real_le (real_pow x0 x2) (real_pow x1 x2)))).
Definition term59 := ((forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_pow y0 (NUMERAL 0)) (real_pow y1 (NUMERAL 0))) /\ (forall y0 : nat, (forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 (S y0)) (real_pow y2 (S y0)))) -> forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0).
Definition term32 (x0 : real) (x1 : nat) := real_mul x0 (real_pow x0 x1).
Definition term82 (x0 : real) (x1 : real) (x2 : nat) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 x1)) -> real_le (real_mul x0 (real_pow x0 x2)) (real_mul x1 (real_pow x1 x2)).
Definition term42 (x0 : nat) := imp ((fun y0 : nat => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) x0).
Definition term31 (x0 : real) (x1 : nat) := real_pow x0 (S x1).
Definition term30 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0))) x1.
Definition term73 := forall y0 : real, True.
Definition term75 (x0 : Prop) := forall y0 : real, x0.
Definition term34 := (((fun y0 : nat => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_le y2 y3)) -> real_le (real_pow y2 y1) (real_pow y3 y1)) y0) -> (fun y1 : nat => forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_le y2 y3)) -> real_le (real_pow y2 y1) (real_pow y3 y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_le y2 y3)) -> real_le (real_pow y2 y1) (real_pow y3 y1)) y0.
Definition term83 (x0 : real) (x1 : nat) := fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 y0)) -> real_le (real_pow x0 (S x1)) (real_pow y0 (S x1)).
Definition term100 (x0 : real) (x1 : real) (x2 : nat) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 x1)) -> real_le (real_pow x0 x2) (real_pow x1 x2).
Definition term60 (x0 : real) := real_pow x0 (NUMERAL 0).
Definition term33 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term89 (x0 : nat) := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_mul y0 (real_pow y0 x0)) (real_mul y1 (real_pow y1 x0)).
Definition term45 (x0 : nat) := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_pow y0 (S x0)) (real_pow y1 (S x0)).
Definition term41 (x0 : nat) := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_pow y0 x0) (real_pow y1 x0).
Definition term37 := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_pow y0 (NUMERAL 0)) (real_pow y1 (NUMERAL 0)).
Definition term23 := forall y0 : real, forall y1 : real, forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_le y0 y2) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y3)))) -> real_le (real_mul y0 y1) (real_mul y2 y3).
Definition term22 (x0 : real) := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_le x0 y1) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y2)))) -> real_le (real_mul x0 y0) (real_mul y1 y2).
Definition term21 (x0 : real) (x1 : real) := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_le x0 y0) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_le x1 y1)))) -> real_le (real_mul x0 x1) (real_mul y0 y1).
Definition term13 (x0 : real) (x1 : real) := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_le x0 x1) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)))) -> real_le (real_mul x0 y0) (real_mul x1 y1).
Definition term11 (x0 : real) := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_le x0 y0) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)))) -> real_le (real_mul x0 y1) (real_mul y0 y2).
Definition term9 := forall y0 : real, forall y1 : real, forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_le y0 y1) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_le y2 y3)))) -> real_le (real_mul y0 y2) (real_mul y1 y3).
Definition term0 := forall y0 : real, forall y1 : nat, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (real_pow y0 y1).
Definition term54 := imp (((fun y0 : nat => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_le y2 y3)) -> real_le (real_pow y2 y1) (real_pow y3 y1)) y0) -> (fun y1 : nat => forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_le y2 y3)) -> real_le (real_pow y2 y1) (real_pow y3 y1)) (S y0))).
Definition term90 (x0 : real) (x1 : real) (x2 : nat) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_le x0 x1) /\ ((real_le (real_of_num (NUMERAL 0)) (real_pow x0 x2)) /\ (real_le (real_pow x0 x2) (real_pow x1 x2))))) -> real_le (real_mul x0 (real_pow x0 x2)) (real_mul x1 (real_pow x1 x2)).
Definition term68 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 x1)) -> True.
Definition term50 := forall y0 : nat, ((fun y1 : nat => forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_le y2 y3)) -> real_le (real_pow y2 y1) (real_pow y3 y1)) y0) -> (fun y1 : nat => forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_le y2 y3)) -> real_le (real_pow y2 y1) (real_pow y3 y1)) (S y0).
Definition term98 (x0 : real) (x1 : nat) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 y0)) -> real_le (real_pow x0 x1) (real_pow y0 x1).
Definition term15 (x0 : real) (x1 : real) (x2 : real) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_le x0 x2) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_le x1 y0)))) -> real_le (real_mul x0 x1) (real_mul x2 y0).
Definition term6 (x0 : real) (x1 : nat) := real_le (real_of_num (NUMERAL 0)) (real_pow x0 x1).
Definition term66 (x0 : real) (x1 : real) := imp ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 x1)).
Definition term101 (x0 : real) (x1 : real) (x2 : nat) := real_le (real_pow x0 x2) (real_pow x1 x2).
Definition term91 (x0 : real) := and (real_le (real_of_num (NUMERAL 0)) x0).
Definition term1 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (real_pow y0 y1)) x0.
Definition term88 (x0 : nat) := fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_mul y0 (real_pow y0 x0)) (real_mul y1 (real_pow y1 x0)).
Definition term87 (x0 : nat) := fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_pow y0 (S x0)) (real_pow y1 (S x0)).
Definition term76 := fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_pow y0 (NUMERAL 0)) (real_pow y1 (NUMERAL 0)).
Definition term2 (x0 : real) := forall y0 : nat, (real_le (real_of_num (NUMERAL 0)) x0) -> real_le (real_of_num (NUMERAL 0)) (real_pow x0 y0).
Definition term19 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_le (real_mul x0 x1) (real_mul x2 x3).
Definition term38 := and ((fun y0 : nat => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) (NUMERAL 0)).
Definition term44 (x0 : nat) := (fun y0 : nat => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) (S x0).
Definition term36 := (fun y0 : nat => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) (NUMERAL 0).
Definition term3 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_le (real_of_num (NUMERAL 0)) x0) -> real_le (real_of_num (NUMERAL 0)) (real_pow x0 y0)) x1.
Definition term95 (x0 : real) (x1 : real) (x2 : nat) := True /\ ((real_le (real_of_num (NUMERAL 0)) (real_pow x0 x2)) /\ (real_le (real_pow x0 x2) (real_pow x1 x2))).
Definition term55 := imp ((forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_pow y0 (NUMERAL 0)) (real_pow y1 (NUMERAL 0))) /\ (forall y0 : nat, (forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 (S y0)) (real_pow y2 (S y0)))).
Definition term20 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (forall y0 : real, forall y1 : real, forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_le y0 y1) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_le y2 y3)))) -> real_le (real_mul y0 y2) (real_mul y1 y3)) -> real_le (real_mul x0 x1) (real_mul x2 x3).
Definition term58 := forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0).
Definition term79 (x0 : real) (x1 : real) (x2 : nat) := real_le (real_pow x0 (S x2)) (real_pow x1 (S x2)).
Definition term81 (x0 : real) (x1 : real) (x2 : nat) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 x1)) -> real_le (real_pow x0 (S x2)) (real_pow x1 (S x2)).
Definition term17 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_le x0 x2) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_le x1 x3)))) -> real_le (real_mul x0 x1) (real_mul x2 x3).
Definition term80 (x0 : real) (x1 : real) (x2 : nat) := real_le (real_mul x0 (real_pow x0 x2)) (real_mul x1 (real_pow x1 x2)).
Definition term5 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term48 := fun y0 : nat => ((fun y1 : nat => forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_le y2 y3)) -> real_le (real_pow y2 y1) (real_pow y3 y1)) y0) -> (fun y1 : nat => forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_le y2 y3)) -> real_le (real_pow y2 y1) (real_pow y3 y1)) (S y0).
Definition term97 (x0 : nat) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_pow y0 x0) (real_pow y1 x0)) x1.
Definition term93 (x0 : real) (x1 : real) (x2 : nat) := (real_le (real_of_num (NUMERAL 0)) (real_pow x0 x2)) /\ (real_le (real_pow x0 x2) (real_pow x1 x2)).
Definition term78 (x0 : real) (x1 : nat) := real_le (real_mul x0 (real_pow x0 x1)).
Definition term7 (x0 : real) (x1 : nat) := (forall y0 : real, forall y1 : nat, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (real_pow y0 y1)) -> real_le (real_of_num (NUMERAL 0)) (real_pow x0 x1).
Definition term27 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_le x0 y0) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_le x1 y1)))) -> real_le (real_mul x0 x1) (real_mul y0 y1)) x2.
Definition term14 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_le x0 x1) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)))) -> real_le (real_mul x0 y0) (real_mul x1 y1)) x2.
Definition term56 := fun y0 : nat => (fun y1 : nat => forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_le y2 y3)) -> real_le (real_pow y2 y1) (real_pow y3 y1)) y0.
Definition term49 := fun y0 : nat => (forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 (S y0)) (real_pow y2 (S y0)).
Definition term28 (x0 : real) := (fun y0 : real => real_le y0 y0) x0.
Definition term52 := ((fun y0 : nat => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_le y2 y3)) -> real_le (real_pow y2 y1) (real_pow y3 y1)) y0) -> (fun y1 : nat => forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_le y2 y3)) -> real_le (real_pow y2 y1) (real_pow y3 y1)) (S y0)).
Definition term70 (x0 : real) := fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 y0)) -> real_le (real_pow x0 (NUMERAL 0)) (real_pow y0 (NUMERAL 0)).
Definition term61 := real_of_num (NUMERAL (BIT1 0)).
Definition term102 (x0 : real) (x1 : real) (x2 : nat) := (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_pow y0 x2) (real_pow y1 x2)) -> real_le (real_pow x0 x2) (real_pow x1 x2).
Definition term18 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_le x0 x1) /\ ((real_le (real_of_num (NUMERAL 0)) x2) /\ (real_le x2 x3))).
Definition term92 (x0 : real) (x1 : real) := and (real_le x0 x1).
Definition term26 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_le x0 y1) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y2)))) -> real_le (real_mul x0 y0) (real_mul y1 y2)) x1.
Definition term12 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_le x0 y0) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)))) -> real_le (real_mul x0 y1) (real_mul y0 y2)) x1.
Definition term16 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_le x0 x2) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_le x1 y0)))) -> real_le (real_mul x0 x1) (real_mul x2 y0)) x3.
Definition term99 (x0 : real) (x1 : nat) (x2 : real) := (fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 y0)) -> real_le (real_pow x0 x1) (real_pow y0 x1)) x2.
Definition term94 (x0 : real) (x1 : real) (x2 : nat) := (real_le x0 x1) /\ ((real_le (real_of_num (NUMERAL 0)) (real_pow x0 x2)) /\ (real_le (real_pow x0 x2) (real_pow x1 x2))).
Definition term86 (x0 : real) (x1 : nat) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 y0)) -> real_le (real_mul x0 (real_pow x0 x1)) (real_mul y0 (real_pow y0 x1)).
Definition term85 (x0 : real) (x1 : nat) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 y0)) -> real_le (real_pow x0 (S x1)) (real_pow y0 (S x1)).
Definition term72 (x0 : real) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 y0)) -> real_le (real_pow x0 (NUMERAL 0)) (real_pow y0 (NUMERAL 0)).
Definition term63 := real_le (real_of_num (NUMERAL (BIT1 0))).
Definition term46 (x0 : nat) := ((fun y0 : nat => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) x0) -> (fun y0 : nat => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) (S x0).
Definition term57 := forall y0 : nat, (fun y1 : nat => forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_le y2 y3)) -> real_le (real_pow y2 y1) (real_pow y3 y1)) y0.
Definition term25 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_le y0 y2) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y3)))) -> real_le (real_mul y0 y1) (real_mul y2 y3)) x0.
Definition term10 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_le y0 y1) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_le y2 y3)))) -> real_le (real_mul y0 y2) (real_mul y1 y3)) x0.
Definition term53 := (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_pow y0 (NUMERAL 0)) (real_pow y1 (NUMERAL 0))) /\ (forall y0 : nat, (forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) -> forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 (S y0)) (real_pow y2 (S y0))).
Definition term62 (x0 : real) := real_le (real_pow x0 (NUMERAL 0)).
Definition term69 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 x1).
