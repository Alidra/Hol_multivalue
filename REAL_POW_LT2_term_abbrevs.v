Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term68 (x0 : real) (x1 : real) := (~ ((NUMERAL 0) = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 x1)).
Definition term40 := fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0).
Definition term48 (x0 : nat) := imp (forall y0 : real, forall y1 : real, ((~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1))) -> real_lt (real_pow y0 x0) (real_pow y1 x0)).
Definition term45 (x0 : nat) := (fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) x0.
Definition term44 := and (forall y0 : real, forall y1 : real, ((~ ((NUMERAL 0) = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1))) -> real_lt (real_pow y0 (NUMERAL 0)) (real_pow y1 (NUMERAL 0))).
Definition term89 (x0 : nat) (x1 : real) (x2 : real) := imp ((~ ((S x0) = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_lt x1 x2))).
Definition term109 (x0 : real) (x1 : real) (x2 : nat) := (real_le (real_of_num (NUMERAL 0)) (real_pow x0 x2)) /\ (real_lt (real_pow x0 x2) (real_pow x1 x2)).
Definition term83 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term56 := forall y0 : nat, (forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> forall y1 : real, forall y2 : real, ((~ ((S y0) = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 (S y0)) (real_pow y2 (S y0)).
Definition term31 (x0 : real) := forall y0 : nat, (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0)).
Definition term4 (x0 : real) (x1 : nat) := (real_le (real_of_num (NUMERAL 0)) x0) -> real_le (real_of_num (NUMERAL 0)) (real_pow x0 x1).
Definition term80 := fun y0 : real => True.
Definition term120 (x0 : nat) := (forall y0 : real, forall y1 : real, ((~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1))) -> real_lt (real_pow y0 x0) (real_pow y1 x0)) -> forall y0 : real, forall y1 : real, ((~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1))) -> real_lt (real_pow y0 x0) (real_pow y1 x0).
Definition term52 (x0 : nat) := (forall y0 : real, forall y1 : real, ((~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1))) -> real_lt (real_pow y0 x0) (real_pow y1 x0)) -> forall y0 : real, forall y1 : real, ((~ ((S x0) = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1))) -> real_lt (real_pow y0 (S x0)) (real_pow y1 (S x0)).
Definition term24 := (forall y0 : real, forall y1 : real, forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_lt y0 y1) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt y2 y3)))) -> real_lt (real_mul y0 y2) (real_mul y1 y3)) -> forall y0 : real, forall y1 : real, forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_lt y0 y2) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y3)))) -> real_lt (real_mul y0 y1) (real_mul y2 y3).
Definition term8 := (forall y0 : real, forall y1 : nat, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (real_pow y0 y1)) -> forall y0 : real, forall y1 : nat, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (real_pow y0 y1).
Definition term112 (x0 : real) (x1 : real) (x2 : nat) := (real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_lt x0 x1) /\ ((real_le (real_of_num (NUMERAL 0)) (real_pow x0 x2)) /\ (real_lt (real_pow x0 x2) (real_pow x1 x2)))).
Definition term64 := ((forall y0 : real, forall y1 : real, ((~ ((NUMERAL 0) = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1))) -> real_lt (real_pow y0 (NUMERAL 0)) (real_pow y1 (NUMERAL 0))) /\ (forall y0 : nat, (forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> forall y1 : real, forall y2 : real, ((~ ((S y0) = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 (S y0)) (real_pow y2 (S y0)))) -> forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0).
Definition term69 (x0 : real) (x1 : real) := False /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 x1)).
Definition term34 (x0 : real) (x1 : nat) := real_mul x0 (real_pow x0 x1).
Definition term106 (x0 : real) (x1 : real) (x2 : nat) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_lt x0 x1) /\ ((real_le (real_of_num (NUMERAL 0)) (real_pow x0 x2)) /\ (real_lt (real_pow x0 x2) (real_pow x1 x2))))) -> real_lt (real_mul x0 (real_pow x0 x2)) (real_mul x1 (real_pow x1 x2)).
Definition term47 (x0 : nat) := imp ((fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) x0).
Definition term33 (x0 : real) (x1 : nat) := real_pow x0 (S x1).
Definition term32 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0))) x1.
Definition term82 := forall y0 : real, True.
Definition term84 (x0 : Prop) := forall y0 : real, x0.
Definition term39 := (((fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : real, forall y3 : real, ((~ (y1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt y2 y3))) -> real_lt (real_pow y2 y1) (real_pow y3 y1)) y0) -> (fun y1 : nat => forall y2 : real, forall y3 : real, ((~ (y1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt y2 y3))) -> real_lt (real_pow y2 y1) (real_pow y3 y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => forall y2 : real, forall y3 : real, ((~ (y1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt y2 y3))) -> real_lt (real_pow y2 y1) (real_pow y3 y1)) y0.
Definition term66 := and (~ ((NUMERAL 0) = (NUMERAL 0))).
Definition term71 (x0 : real) := real_pow x0 (NUMERAL 0).
Definition term38 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term103 (x0 : nat) := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_mul y0 (real_pow y0 x0)) (real_mul y1 (real_pow y1 x0)).
Definition term50 (x0 : nat) := forall y0 : real, forall y1 : real, ((~ ((S x0) = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1))) -> real_lt (real_pow y0 (S x0)) (real_pow y1 (S x0)).
Definition term46 (x0 : nat) := forall y0 : real, forall y1 : real, ((~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1))) -> real_lt (real_pow y0 x0) (real_pow y1 x0).
Definition term42 := forall y0 : real, forall y1 : real, ((~ ((NUMERAL 0) = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1))) -> real_lt (real_pow y0 (NUMERAL 0)) (real_pow y1 (NUMERAL 0)).
Definition term23 := forall y0 : real, forall y1 : real, forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_lt y0 y2) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y3)))) -> real_lt (real_mul y0 y1) (real_mul y2 y3).
Definition term22 (x0 : real) := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_lt x0 y1) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y2)))) -> real_lt (real_mul x0 y0) (real_mul y1 y2).
Definition term21 (x0 : real) (x1 : real) := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_lt x0 y0) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_lt x1 y1)))) -> real_lt (real_mul x0 x1) (real_mul y0 y1).
Definition term13 (x0 : real) (x1 : real) := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_lt x0 x1) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)))) -> real_lt (real_mul x0 y0) (real_mul x1 y1).
Definition term11 (x0 : real) := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_lt x0 y0) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2)))) -> real_lt (real_mul x0 y1) (real_mul y0 y2).
Definition term9 := forall y0 : real, forall y1 : real, forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_lt y0 y1) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt y2 y3)))) -> real_lt (real_mul y0 y2) (real_mul y1 y3).
Definition term0 := forall y0 : real, forall y1 : nat, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (real_pow y0 y1).
Definition term59 := imp (((fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : real, forall y3 : real, ((~ (y1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt y2 y3))) -> real_lt (real_pow y2 y1) (real_pow y3 y1)) y0) -> (fun y1 : nat => forall y2 : real, forall y3 : real, ((~ (y1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt y2 y3))) -> real_lt (real_pow y2 y1) (real_pow y3 y1)) (S y0))).
Definition term67 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 x1).
Definition term91 (x0 : real) (x1 : nat) := real_lt (real_pow x0 (S x1)).
Definition term65 := ~ ((NUMERAL 0) = (NUMERAL 0)).
Definition term19 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_lt (real_mul x0 x1) (real_mul x2 x3).
Definition term88 (x0 : real) (x1 : real) := True /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 x1)).
Definition term97 (x0 : real) (x1 : nat) := fun y0 : real => ((~ ((S x1) = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 y0))) -> real_lt (real_pow x0 (S x1)) (real_pow y0 (S x1)).
Definition term55 := forall y0 : nat, ((fun y1 : nat => forall y2 : real, forall y3 : real, ((~ (y1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt y2 y3))) -> real_lt (real_pow y2 y1) (real_pow y3 y1)) y0) -> (fun y1 : nat => forall y2 : real, forall y3 : real, ((~ (y1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt y2 y3))) -> real_lt (real_pow y2 y1) (real_pow y3 y1)) (S y0).
Definition term114 (x0 : real) (x1 : nat) := forall y0 : real, ((~ (x1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 y0))) -> real_lt (real_pow x0 x1) (real_pow y0 x1).
Definition term15 (x0 : real) (x1 : real) (x2 : real) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_lt x0 x2) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_lt x1 y0)))) -> real_lt (real_mul x0 x1) (real_mul x2 y0).
Definition term30 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term6 (x0 : real) (x1 : nat) := real_le (real_of_num (NUMERAL 0)) (real_pow x0 x1).
Definition term108 (x0 : real) (x1 : real) := and (real_lt x0 x1).
Definition term86 (x0 : nat) := and (~ ((S x0) = (NUMERAL 0))).
Definition term107 (x0 : real) := and (real_le (real_of_num (NUMERAL 0)) x0).
Definition term1 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (real_pow y0 y1)) x0.
Definition term102 (x0 : nat) := fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_mul y0 (real_pow y0 x0)) (real_mul y1 (real_pow y1 x0)).
Definition term101 (x0 : nat) := fun y0 : real => forall y1 : real, ((~ ((S x0) = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1))) -> real_lt (real_pow y0 (S x0)) (real_pow y1 (S x0)).
Definition term85 := fun y0 : real => forall y1 : real, ((~ ((NUMERAL 0) = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1))) -> real_lt (real_pow y0 (NUMERAL 0)) (real_pow y1 (NUMERAL 0)).
Definition term94 (x0 : real) (x1 : real) (x2 : nat) := real_lt (real_mul x0 (real_pow x0 x2)) (real_mul x1 (real_pow x1 x2)).
Definition term2 (x0 : real) := forall y0 : nat, (real_le (real_of_num (NUMERAL 0)) x0) -> real_le (real_of_num (NUMERAL 0)) (real_pow x0 y0).
Definition term111 (x0 : real) (x1 : real) (x2 : nat) := True /\ ((real_le (real_of_num (NUMERAL 0)) (real_pow x0 x2)) /\ (real_lt (real_pow x0 x2) (real_pow x1 x2))).
Definition term98 (x0 : real) (x1 : nat) := fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 y0)) -> real_lt (real_mul x0 (real_pow x0 x1)) (real_mul y0 (real_pow y0 x1)).
Definition term43 := and ((fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) (NUMERAL 0)).
Definition term49 (x0 : nat) := (fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) (S x0).
Definition term41 := (fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) (NUMERAL 0).
Definition term3 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_le (real_of_num (NUMERAL 0)) x0) -> real_le (real_of_num (NUMERAL 0)) (real_pow x0 y0)) x1.
Definition term60 := imp ((forall y0 : real, forall y1 : real, ((~ ((NUMERAL 0) = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1))) -> real_lt (real_pow y0 (NUMERAL 0)) (real_pow y1 (NUMERAL 0))) /\ (forall y0 : nat, (forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> forall y1 : real, forall y2 : real, ((~ ((S y0) = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 (S y0)) (real_pow y2 (S y0)))).
Definition term77 (x0 : real) (x1 : real) := ((~ ((NUMERAL 0) = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 x1))) -> real_lt (real_pow x0 (NUMERAL 0)) (real_pow x1 (NUMERAL 0)).
Definition term73 (x0 : real) := real_lt (real_pow x0 (NUMERAL 0)).
Definition term63 := forall y0 : nat, forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0).
Definition term87 (x0 : nat) (x1 : real) (x2 : real) := (~ ((S x0) = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_lt x1 x2)).
Definition term29 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term74 := real_lt (real_of_num (NUMERAL (BIT1 0))).
Definition term17 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_lt x0 x2) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_lt x1 x3)))) -> real_lt (real_mul x0 x1) (real_mul x2 x3).
Definition term93 (x0 : real) (x1 : real) (x2 : nat) := real_lt (real_pow x0 (S x2)) (real_pow x1 (S x2)).
Definition term5 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term36 (x0 : nat) := ~ ((S x0) = (NUMERAL 0)).
Definition term79 (x0 : real) := fun y0 : real => ((~ ((NUMERAL 0) = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 y0))) -> real_lt (real_pow x0 (NUMERAL 0)) (real_pow y0 (NUMERAL 0)).
Definition term76 := real_lt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term78 := False -> real_lt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term53 := fun y0 : nat => ((fun y1 : nat => forall y2 : real, forall y3 : real, ((~ (y1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt y2 y3))) -> real_lt (real_pow y2 y1) (real_pow y3 y1)) y0) -> (fun y1 : nat => forall y2 : real, forall y3 : real, ((~ (y1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt y2 y3))) -> real_lt (real_pow y2 y1) (real_pow y3 y1)) (S y0).
Definition term113 (x0 : nat) (x1 : real) := (fun y0 : real => forall y1 : real, ((~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1))) -> real_lt (real_pow y0 x0) (real_pow y1 x0)) x1.
Definition term122 (x0 : nat) := and (~ (x0 = (NUMERAL 0))).
Definition term75 (x0 : real) (x1 : real) := real_lt (real_pow x0 (NUMERAL 0)) (real_pow x1 (NUMERAL 0)).
Definition term7 (x0 : real) (x1 : nat) := (forall y0 : real, forall y1 : nat, (real_le (real_of_num (NUMERAL 0)) y0) -> real_le (real_of_num (NUMERAL 0)) (real_pow y0 y1)) -> real_le (real_of_num (NUMERAL 0)) (real_pow x0 x1).
Definition term115 (x0 : real) (x1 : nat) (x2 : real) := (fun y0 : real => ((~ (x1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 y0))) -> real_lt (real_pow x0 x1) (real_pow y0 x1)) x2.
Definition term27 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_lt x0 y0) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_lt x1 y1)))) -> real_lt (real_mul x0 x1) (real_mul y0 y1)) x2.
Definition term14 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_lt x0 x1) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)))) -> real_lt (real_mul x0 y0) (real_mul x1 y1)) x2.
Definition term61 := fun y0 : nat => (fun y1 : nat => forall y2 : real, forall y3 : real, ((~ (y1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt y2 y3))) -> real_lt (real_pow y2 y1) (real_pow y3 y1)) y0.
Definition term35 (x0 : nat) := (fun y0 : nat => ~ ((S y0) = (NUMERAL 0))) x0.
Definition term54 := fun y0 : nat => (forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> forall y1 : real, forall y2 : real, ((~ ((S y0) = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 (S y0)) (real_pow y2 (S y0)).
Definition term116 (x0 : real) (x1 : real) (x2 : nat) := ((~ (x2 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 x1))) -> real_lt (real_pow x0 x2) (real_pow x1 x2).
Definition term118 (x0 : real) (x1 : real) (x2 : nat) := real_lt (real_pow x0 x2) (real_pow x1 x2).
Definition term57 := ((fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => forall y2 : real, forall y3 : real, ((~ (y1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt y2 y3))) -> real_lt (real_pow y2 y1) (real_pow y3 y1)) y0) -> (fun y1 : nat => forall y2 : real, forall y3 : real, ((~ (y1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt y2 y3))) -> real_lt (real_pow y2 y1) (real_pow y3 y1)) (S y0)).
Definition term16 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_lt x0 x2) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_lt x1 y0)))) -> real_lt (real_mul x0 x1) (real_mul x2 y0)) x3.
Definition term72 := real_of_num (NUMERAL (BIT1 0)).
Definition term95 (x0 : real) (x1 : real) (x2 : nat) := ((~ ((S x2) = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 x1))) -> real_lt (real_pow x0 (S x2)) (real_pow x1 (S x2)).
Definition term18 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_lt x0 x1) /\ ((real_le (real_of_num (NUMERAL 0)) x2) /\ (real_lt x2 x3))).
Definition term117 (x0 : nat) (x1 : real) (x2 : real) := (~ (x0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_lt x1 x2)).
Definition term37 (x0 : nat) := (~ ((S x0) = (NUMERAL 0))) -> ((S x0) = (NUMERAL 0)) = False.
Definition term119 (x0 : real) (x1 : real) (x2 : nat) := (forall y0 : real, forall y1 : real, ((~ (x2 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1))) -> real_lt (real_pow y0 x2) (real_pow y1 x2)) -> real_lt (real_pow x0 x2) (real_pow x1 x2).
Definition term110 (x0 : real) (x1 : real) (x2 : nat) := (real_lt x0 x1) /\ ((real_le (real_of_num (NUMERAL 0)) (real_pow x0 x2)) /\ (real_lt (real_pow x0 x2) (real_pow x1 x2))).
Definition term121 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term90 (x0 : real) (x1 : real) := imp ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 x1)).
Definition term105 (x0 : real) := real_mul x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term26 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_lt x0 y1) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y2)))) -> real_lt (real_mul x0 y0) (real_mul y1 y2)) x1.
Definition term12 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_lt x0 y0) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2)))) -> real_lt (real_mul x0 y1) (real_mul y0 y2)) x1.
Definition term100 (x0 : real) (x1 : nat) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 y0)) -> real_lt (real_mul x0 (real_pow x0 x1)) (real_mul y0 (real_pow y0 x1)).
Definition term99 (x0 : real) (x1 : nat) := forall y0 : real, ((~ ((S x1) = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 y0))) -> real_lt (real_pow x0 (S x1)) (real_pow y0 (S x1)).
Definition term81 (x0 : real) := forall y0 : real, ((~ ((NUMERAL 0) = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 y0))) -> real_lt (real_pow x0 (NUMERAL 0)) (real_pow y0 (NUMERAL 0)).
Definition term70 (x0 : real) (x1 : real) := imp ((~ ((NUMERAL 0) = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 x1))).
Definition term96 (x0 : real) (x1 : real) (x2 : nat) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 x1)) -> real_lt (real_mul x0 (real_pow x0 x2)) (real_mul x1 (real_pow x1 x2)).
Definition term92 (x0 : real) (x1 : nat) := real_lt (real_mul x0 (real_pow x0 x1)).
Definition term104 (x0 : real) := (fun y0 : real => (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0) x0.
Definition term51 (x0 : nat) := ((fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) x0) -> (fun y0 : nat => forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) (S x0).
Definition term62 := forall y0 : nat, (fun y1 : nat => forall y2 : real, forall y3 : real, ((~ (y1 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt y2 y3))) -> real_lt (real_pow y2 y1) (real_pow y3 y1)) y0.
Definition term25 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_lt y0 y2) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y3)))) -> real_lt (real_mul y0 y1) (real_mul y2 y3)) x0.
Definition term10 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_lt y0 y1) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt y2 y3)))) -> real_lt (real_mul y0 y2) (real_mul y1 y3)) x0.
Definition term58 := (forall y0 : real, forall y1 : real, ((~ ((NUMERAL 0) = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1))) -> real_lt (real_pow y0 (NUMERAL 0)) (real_pow y1 (NUMERAL 0))) /\ (forall y0 : nat, (forall y1 : real, forall y2 : real, ((~ (y0 = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) -> forall y1 : real, forall y2 : real, ((~ ((S y0) = (NUMERAL 0))) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2))) -> real_lt (real_pow y1 (S y0)) (real_pow y2 (S y0))).
Definition term28 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term20 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (forall y0 : real, forall y1 : real, forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_lt y0 y1) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt y2 y3)))) -> real_lt (real_mul y0 y2) (real_mul y1 y3)) -> real_lt (real_mul x0 x1) (real_mul x2 x3).
