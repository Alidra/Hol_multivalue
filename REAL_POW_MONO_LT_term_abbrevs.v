Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term109 (x0 : nat) (x1 : real) (x2 : nat) := real_lt (real_mul (real_pow x1 x0) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_pow x1 x0) (real_pow x1 (S x2))).
Definition term71 := fun y0 : real => (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0.
Definition term64 (x0 : real) (x1 : real) (x2 : real) := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y1 y2)) -> real_lt (real_mul y0 y1) (real_mul y0 y2)) -> real_lt (real_mul x1 x0) (real_mul x1 x2).
Definition term146 (x0 : real) := and (real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S (NUMERAL 0)))).
Definition term80 (x0 : nat) (x1 : real) (x2 : nat) := (fun y0 : nat => (real_pow x1 (Nat.add x0 y0)) = (real_mul (real_pow x1 x0) (real_pow x1 y0))) x2.
Definition term151 (x0 : real) (x1 : nat) := (fun y0 : nat => real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y0))) (S x1).
Definition term143 (x0 : real) := (fun y0 : nat => real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y0))) (NUMERAL 0).
Definition term187 (x0 : nat) := (fun y0 : nat => (Peano.le 0 (BIT1 y0)) = True) x0.
Definition term121 (x0 : nat) := (fun y0 : nat => (Peano.lt 0 (BIT1 y0)) = True) x0.
Definition term104 (x0 : nat) (x1 : real) (x2 : nat) := real_mul (real_pow x1 x0) (real_pow x1 (S x2)).
Definition term204 (x0 : real) (x1 : nat) := (real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) /\ ((real_lt (real_of_num (NUMERAL (BIT1 0))) x0) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) /\ (real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S x1))))).
Definition term131 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term103 (x0 : real) (x1 : nat) (x2 : nat) := real_pow x0 (Nat.add x1 (S x2)).
Definition term202 (x0 : real) (x1 : nat) := (real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) /\ (real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S x1))).
Definition term113 := real_of_num (NUMERAL 0).
Definition term181 := ((Peano.le 0 0) = True) /\ ((forall y0 : nat, (Peano.le (BIT0 y0) 0) = (Peano.le y0 0)) /\ ((forall y0 : nat, (Peano.le (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1))))))))).
Definition term180 := (forall y0 : nat, forall y1 : nat, (Peano.le (NUMERAL y0) (NUMERAL y1)) = (Peano.le y0 y1)) /\ (((Peano.le 0 0) = True) /\ ((forall y0 : nat, (Peano.le (BIT0 y0) 0) = (Peano.le y0 0)) /\ ((forall y0 : nat, (Peano.le (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1)))))))))).
Definition term182 := (forall y0 : nat, (Peano.le (BIT0 y0) 0) = (Peano.le y0 0)) /\ ((forall y0 : nat, (Peano.le (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1)))))))).
Definition term118 := (forall y0 : nat, (Peano.lt 0 (BIT0 y0)) = (Peano.lt 0 y0)) /\ ((forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1)))))).
Definition term60 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt x0 y0)) -> real_lt (real_mul x1 x0) (real_mul x1 y0)) x2.
Definition term136 := and (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term160 (x0 : real) := (real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S (NUMERAL 0)))) /\ (forall y0 : nat, (real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y0))) -> real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S (S y0)))).
Definition term20 := fun y0 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0.
Definition term25 (x0 : real) := forall y0 : nat, (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0)).
Definition term165 (x0 : real) := forall y0 : nat, real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y0)).
Definition term67 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y1 y2)) -> real_lt (real_mul y0 y1) (real_mul y0 y2)) -> forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_lt y0 y2)) -> real_lt (real_mul y1 y0) (real_mul y1 y2).
Definition term54 := (forall y0 : real, forall y1 : nat, (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (real_pow y0 y1)) -> forall y0 : real, forall y1 : nat, (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (real_pow y0 y1).
Definition term43 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> forall y0 : real, forall y1 : real, (exists y2 : real, (real_lt y0 y2) /\ (real_lt y2 y1)) -> real_lt y0 y1.
Definition term15 := (forall y0 : real, forall y1 : real, forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_lt y0 y1) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt y2 y3)))) -> real_lt (real_mul y0 y2) (real_mul y1 y3)) -> forall y0 : real, forall y1 : real, forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_lt y0 y2) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y3)))) -> real_lt (real_mul y0 y1) (real_mul y2 y3).
Definition term38 (x0 : real) (x1 : real) := exists y0 : real, (real_lt x0 y0) /\ (real_lt y0 x1).
Definition term195 (x0 : nat) := forall y0 : nat, (real_le (real_of_num x0) (real_of_num y0)) = (Peano.le x0 y0).
Definition term191 (x0 : nat) := forall y0 : nat, (Peano.le (NUMERAL x0) (NUMERAL y0)) = (Peano.le x0 y0).
Definition term129 (x0 : nat) := forall y0 : nat, (real_lt (real_of_num x0) (real_of_num y0)) = (Peano.lt x0 y0).
Definition term125 (x0 : nat) := forall y0 : nat, (Peano.lt (NUMERAL x0) (NUMERAL y0)) = (Peano.lt x0 y0).
Definition term28 (x0 : real) (x1 : nat) := real_mul x0 (real_pow x0 x1).
Definition term164 (x0 : real) := forall y0 : nat, (fun y1 : nat => real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y1))) y0.
Definition term144 (x0 : real) := real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S (NUMERAL 0))).
Definition term159 (x0 : real) := ((fun y0 : nat => real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y1))) y0) -> (fun y1 : nat => real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y1))) (S y0)).
Definition term84 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 (S y1))).
Definition term27 (x0 : real) (x1 : nat) := real_pow x0 (S x1).
Definition term178 (x0 : real) (x1 : nat) := real_lt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x0 (S x1))).
Definition term26 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0))) x1.
Definition term89 (x0 : real) (x1 : nat) (x2 : nat) := (real_lt (real_of_num (NUMERAL (BIT1 0))) x0) /\ (exists y0 : nat, x1 = (Nat.add x2 (S y0))).
Definition term153 (x0 : real) (x1 : nat) := ((fun y0 : nat => real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y0))) x1) -> (fun y0 : nat => real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y0))) (S x1).
Definition term141 (x0 : real) := (((fun y0 : nat => real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y1))) y0) -> (fun y1 : nat => real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y1))) (S y0))) -> forall y0 : nat, (fun y1 : nat => real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y1))) y0.
Definition term201 := and (real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term175 (x0 : real) := real_pow x0 (NUMERAL 0).
Definition term21 := fun y0 : real => y0 = (real_mul (real_of_num (NUMERAL (BIT1 0))) y0).
Definition term140 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term133 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term66 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_lt y0 y2)) -> real_lt (real_mul y1 y0) (real_mul y1 y2).
Definition term65 (x0 : real) := forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt x0 y1)) -> real_lt (real_mul y0 x0) (real_mul y0 y1).
Definition term57 (x0 : real) := forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt y0 y1)) -> real_lt (real_mul x0 y0) (real_mul x0 y1).
Definition term55 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y1 y2)) -> real_lt (real_mul y0 y1) (real_mul y0 y2).
Definition term46 := forall y0 : real, forall y1 : nat, (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (real_pow y0 y1).
Definition term42 := forall y0 : real, forall y1 : real, (exists y2 : real, (real_lt y0 y2) /\ (real_lt y2 y1)) -> real_lt y0 y1.
Definition term31 (x0 : real) := forall y0 : real, forall y1 : real, ((real_lt x0 y0) /\ (real_lt y0 y1)) -> real_lt x0 y1.
Definition term29 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2.
Definition term14 := forall y0 : real, forall y1 : real, forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_lt y0 y2) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y3)))) -> real_lt (real_mul y0 y1) (real_mul y2 y3).
Definition term13 (x0 : real) := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_lt x0 y1) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y2)))) -> real_lt (real_mul x0 y0) (real_mul y1 y2).
Definition term12 (x0 : real) (x1 : real) := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_lt x0 y0) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_lt x1 y1)))) -> real_lt (real_mul x0 x1) (real_mul y0 y1).
Definition term4 (x0 : real) (x1 : real) := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_lt x0 x1) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)))) -> real_lt (real_mul x0 y0) (real_mul x1 y1).
Definition term2 (x0 : real) := forall y0 : real, forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_lt x0 y0) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2)))) -> real_lt (real_mul x0 y1) (real_mul y0 y2).
Definition term0 := forall y0 : real, forall y1 : real, forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_lt y0 y1) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt y2 y3)))) -> real_lt (real_mul y0 y2) (real_mul y1 y3).
Definition term161 (x0 : real) := imp (((fun y0 : nat => real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y0))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y1))) y0) -> (fun y1 : nat => real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y1))) (S y0))).
Definition term150 (x0 : real) (x1 : nat) := imp (real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S x1))).
Definition term10 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_lt (real_mul x0 x1) (real_mul x2 x3).
Definition term88 (x0 : real) (x1 : nat) (x2 : nat) := (real_lt (real_of_num (NUMERAL (BIT1 0))) x0) /\ (Peano.lt x1 x2).
Definition term78 (x0 : real) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (real_pow x0 (Nat.add y0 y1)) = (real_mul (real_pow x0 y0) (real_pow x0 y1))) x1.
Definition term87 (x0 : real) := and (real_lt (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term37 (x0 : real) (x1 : real) := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) -> real_lt x0 x1.
Definition term188 (x0 : nat) := Peano.le 0 (BIT1 x0).
Definition term157 (x0 : real) := forall y0 : nat, ((fun y1 : nat => real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y1))) y0) -> (fun y1 : nat => real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y1))) (S y0).
Definition term208 (x0 : nat) (x1 : nat) := forall y0 : real, ((real_lt (real_of_num (NUMERAL (BIT1 0))) y0) /\ (Peano.lt x0 x1)) -> real_lt (real_pow y0 x0) (real_pow y0 x1).
Definition term59 (x0 : real) (x1 : real) := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt x0 y0)) -> real_lt (real_mul x1 x0) (real_mul x1 y0).
Definition term6 (x0 : real) (x1 : real) (x2 : real) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_lt x0 x2) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_lt x1 y0)))) -> real_lt (real_mul x0 x1) (real_mul x2 y0).
Definition term110 (x0 : nat) (x1 : real) (x2 : nat) := ((real_lt (real_of_num (NUMERAL 0)) (real_pow x1 x0)) /\ (real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x1 (S x2)))) -> real_lt (real_mul (real_pow x1 x0) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_pow x1 x0) (real_pow x1 (S x2))).
Definition term50 (x0 : real) (x1 : nat) := (real_lt (real_of_num (NUMERAL 0)) x0) -> real_lt (real_of_num (NUMERAL 0)) (real_pow x0 x1).
Definition term107 (x0 : real) (x1 : nat) := real_mul (real_pow x0 x1) (real_of_num (NUMERAL (BIT1 0))).
Definition term81 (x0 : real) (x1 : nat) (x2 : nat) := real_pow x0 (Nat.add x1 x2).
Definition term23 := forall y0 : real, y0 = (real_mul (real_of_num (NUMERAL (BIT1 0))) y0).
Definition term114 := (forall y0 : nat, forall y1 : nat, (Peano.lt (NUMERAL y0) (NUMERAL y1)) = (Peano.lt y0 y1)) /\ (((Peano.lt 0 0) = False) /\ ((forall y0 : nat, (Peano.lt (BIT0 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt 0 (BIT0 y0)) = (Peano.lt 0 y0)) /\ ((forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1)))))))))).
Definition term145 (x0 : real) := and ((fun y0 : nat => real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y0))) (NUMERAL 0)).
Definition term47 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (real_pow y0 y1)) x0.
Definition term100 (x0 : real) (x1 : nat) (x2 : nat) := real_lt (real_pow x0 x1) (real_pow x0 (Nat.add x1 (S x2))).
Definition term62 (x0 : real) (x1 : real) (x2 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt x1 x2).
Definition term156 (x0 : real) := fun y0 : nat => (real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y0))) -> real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S (S y0))).
Definition term199 := Peano.le (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term48 (x0 : real) := forall y0 : nat, (real_lt (real_of_num (NUMERAL 0)) x0) -> real_lt (real_of_num (NUMERAL 0)) (real_pow x0 y0).
Definition term207 (x0 : nat) (x1 : real) (x2 : nat) := (exists y0 : nat, x2 = (Nat.add x0 (S y0))) -> real_lt (real_pow x1 x0) (real_pow x1 x2).
Definition term203 (x0 : real) (x1 : nat) := (real_lt (real_of_num (NUMERAL (BIT1 0))) x0) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) /\ (real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S x1)))).
Definition term24 (x0 : real) := (fun y0 : real => y0 = (real_mul (real_of_num (NUMERAL (BIT1 0))) y0)) x0.
Definition term41 (x0 : real) := forall y0 : real, (exists y1 : real, (real_lt x0 y1) /\ (real_lt y1 y0)) -> real_lt x0 y0.
Definition term155 (x0 : real) := fun y0 : nat => ((fun y1 : nat => real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y1))) y0) -> (fun y1 : nat => real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y1))) (S y0).
Definition term196 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_le (real_of_num x0) (real_of_num y0)) = (Peano.le x0 y0)) x1.
Definition term192 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le (NUMERAL x0) (NUMERAL y0)) = (Peano.le x0 y0)) x1.
Definition term132 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term147 (x0 : real) (x1 : nat) := (fun y0 : nat => real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y0))) x1.
Definition term210 := forall y0 : nat, forall y1 : nat, forall y2 : real, ((real_lt (real_of_num (NUMERAL (BIT1 0))) y2) /\ (Peano.lt y0 y1)) -> real_lt (real_pow y2 y0) (real_pow y2 y1).
Definition term209 (x0 : nat) := forall y0 : nat, forall y1 : real, ((real_lt (real_of_num (NUMERAL (BIT1 0))) y1) /\ (Peano.lt x0 y0)) -> real_lt (real_pow y1 x0) (real_pow y1 y0).
Definition term189 := forall y0 : nat, forall y1 : nat, (Peano.le (NUMERAL y0) (NUMERAL y1)) = (Peano.le y0 y1).
Definition term123 := forall y0 : nat, forall y1 : nat, (Peano.lt (NUMERAL y0) (NUMERAL y1)) = (Peano.lt y0 y1).
Definition term77 (x0 : real) := forall y0 : nat, forall y1 : nat, (real_pow x0 (Nat.add y0 y1)) = (real_mul (real_pow x0 y0) (real_pow x0 y1)).
Definition term138 (x0 : real) := exists y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 x0).
Definition term19 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term97 (x0 : nat) (x1 : real) := fun y0 : nat => real_lt (real_pow x1 x0) (real_pow x1 y0).
Definition term22 := forall y0 : real, (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0.
Definition term169 := real_lt (real_of_num (NUMERAL (BIT1 0))).
Definition term36 (x0 : real) (x1 : real) (x2 : real) := (real_lt x0 x1) /\ (real_lt x1 x2).
Definition term82 (x0 : nat) (x1 : real) (x2 : nat) := real_mul (real_pow x1 x0) (real_pow x1 x2).
Definition term61 (x0 : real) (x1 : real) (x2 : real) := ((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt x0 x2)) -> real_lt (real_mul x1 x0) (real_mul x1 x2).
Definition term166 (x0 : real) := ((real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S (NUMERAL 0)))) /\ (forall y0 : nat, (real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y0))) -> real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S (S y0))))) -> forall y0 : nat, real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y0)).
Definition term122 (x0 : nat) := Peano.lt 0 (BIT1 x0).
Definition term115 := ((Peano.lt 0 0) = False) /\ ((forall y0 : nat, (Peano.lt (BIT0 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt 0 (BIT0 y0)) = (Peano.lt 0 y0)) /\ ((forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1))))))))).
Definition term98 (x0 : nat) (x1 : real) (x2 : nat) := (fun y0 : nat => real_lt (real_pow x1 x0) (real_pow x1 y0)) x2.
Definition term44 (x0 : real) := (fun y0 : real => forall y1 : real, (exists y2 : real, (real_lt y0 y2) /\ (real_lt y2 y1)) -> real_lt y0 y1) x0.
Definition term149 (x0 : real) (x1 : nat) := imp ((fun y0 : nat => real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y0))) x1).
Definition term176 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term52 (x0 : real) (x1 : nat) := real_lt (real_of_num (NUMERAL 0)) (real_pow x0 x1).
Definition term79 (x0 : nat) (x1 : real) := forall y0 : nat, (real_pow x1 (Nat.add x0 y0)) = (real_mul (real_pow x1 x0) (real_pow x1 y0)).
Definition term75 (x0 : real) := (fun y0 : real => y0 = (real_mul y0 (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term8 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_lt x0 x2) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_lt x1 x3)))) -> real_lt (real_mul x0 x1) (real_mul x2 x3).
Definition term130 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_lt (real_of_num x0) (real_of_num y0)) = (Peano.lt x0 y0)) x1.
Definition term126 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt (NUMERAL x0) (NUMERAL y0)) = (Peano.lt x0 y0)) x1.
Definition term168 (x0 : real) := real_mul x0 (real_pow x0 (NUMERAL 0)).
Definition term40 (x0 : real) (x1 : real) := (exists y0 : real, (real_lt x0 y0) /\ (real_lt y0 x1)) -> real_lt x0 x1.
Definition term99 (x0 : real) (x1 : nat) (x2 : nat) := (fun y0 : nat => real_lt (real_pow x0 x1) (real_pow x0 y0)) (Nat.add x1 (S x2)).
Definition term86 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 (S y0)).
Definition term34 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_lt x1 x0) /\ (real_lt x0 y0)) -> real_lt x1 y0) x2.
Definition term112 (x0 : real) := (exists y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 x0)) -> real_lt (real_of_num (NUMERAL 0)) x0.
Definition term173 (x0 : real) (x1 : nat) := real_lt (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 (real_pow x0 (S x1))).
Definition term106 (x0 : nat) (x1 : real) (x2 : nat) := real_lt (real_pow x1 x0) (real_mul (real_pow x1 x0) (real_pow x1 (S x2))).
Definition term69 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt x0 y1)) -> real_lt (real_mul y0 x0) (real_mul y0 y1)) x1.
Definition term58 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt y0 y1)) -> real_lt (real_mul x0 y0) (real_mul x0 y1)) x1.
Definition term32 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_lt x0 y0) /\ (real_lt y0 y1)) -> real_lt x0 y1) x1.
Definition term49 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_lt (real_of_num (NUMERAL 0)) x0) -> real_lt (real_of_num (NUMERAL 0)) (real_pow x0 y0)) x1.
Definition term108 (x0 : real) (x1 : nat) := real_lt (real_mul (real_pow x0 x1) (real_of_num (NUMERAL (BIT1 0)))).
Definition term90 (x0 : real) (x1 : nat) (x2 : nat) := imp ((real_lt (real_of_num (NUMERAL (BIT1 0))) x0) /\ (Peano.lt x1 x2)).
Definition term51 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) x0.
Definition term139 (x0 : real) := fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 x0).
Definition term18 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_lt x0 y0) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_lt x1 y1)))) -> real_lt (real_mul x0 x1) (real_mul y0 y1)) x2.
Definition term5 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_lt x0 x1) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)))) -> real_lt (real_mul x0 y0) (real_mul x1 y1)) x2.
Definition term137 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) /\ (real_lt (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term194 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_le (real_of_num y0) (real_of_num y1)) = (Peano.le y0 y1)) x0.
Definition term190 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le (NUMERAL y0) (NUMERAL y1)) = (Peano.le y0 y1)) x0.
Definition term128 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_lt (real_of_num y0) (real_of_num y1)) = (Peano.lt y0 y1)) x0.
Definition term124 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (NUMERAL y0) (NUMERAL y1)) = (Peano.lt y0 y1)) x0.
Definition term83 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 (S y2)))) x0.
Definition term142 (x0 : real) := fun y0 : nat => real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y0)).
Definition term45 (x0 : real) (x1 : real) := (fun y0 : real => (exists y1 : real, (real_lt x0 y1) /\ (real_lt y1 y0)) -> real_lt x0 y0) x1.
Definition term76 (x0 : real) := (fun y0 : real => forall y1 : nat, forall y2 : nat, (real_pow y0 (Nat.add y1 y2)) = (real_mul (real_pow y0 y1) (real_pow y0 y2))) x0.
Definition term171 (x0 : real) (x1 : nat) := real_pow x0 (S (S x1)).
Definition term73 := forall y0 : real, (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0.
Definition term154 (x0 : real) (x1 : nat) := (real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S x1))) -> real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S (S x1))).
Definition term7 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_lt x0 x2) /\ ((real_le (real_of_num (NUMERAL 0)) x1) /\ (real_lt x1 y0)))) -> real_lt (real_mul x0 x1) (real_mul x2 y0)) x3.
Definition term179 (x0 : real) (x1 : nat) := ((real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) /\ ((real_lt (real_of_num (NUMERAL (BIT1 0))) x0) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) /\ (real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S x1)))))) -> real_lt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 (real_pow x0 (S x1))).
Definition term200 := Peano.le 0 (BIT1 0).
Definition term206 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.add x1 (S y0)).
Definition term111 := real_of_num (NUMERAL (BIT1 0)).
Definition term33 (x0 : real) (x1 : real) := forall y0 : real, ((real_lt x1 x0) /\ (real_lt x0 y0)) -> real_lt x1 y0.
Definition term193 (x0 : nat) (x1 : nat) := Peano.le (NUMERAL x0) (NUMERAL x1).
Definition term177 := real_lt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term96 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term9 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_lt x0 x1) /\ ((real_le (real_of_num (NUMERAL 0)) x2) /\ (real_lt x2 x3))).
Definition term127 (x0 : nat) (x1 : nat) := Peano.lt (NUMERAL x0) (NUMERAL x1).
Definition term94 (x0 : nat) (x1 : real) (x2 : nat) := ((real_lt (real_of_num (NUMERAL (BIT1 0))) x1) /\ (exists y0 : nat, x2 = (Nat.add x0 (S y0)))) -> real_lt (real_pow x1 x0) (real_pow x1 x2).
Definition term63 (x0 : real) (x1 : real) (x2 : real) := real_lt (real_mul x1 x0) (real_mul x1 x2).
Definition term92 (x0 : nat) (x1 : real) (x2 : nat) := real_lt (real_pow x1 x0) (real_pow x1 x2).
Definition term162 (x0 : real) := imp ((real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S (NUMERAL 0)))) /\ (forall y0 : nat, (real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y0))) -> real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S (S y0))))).
Definition term91 (x0 : real) (x1 : nat) (x2 : nat) := imp ((real_lt (real_of_num (NUMERAL (BIT1 0))) x0) /\ (exists y0 : nat, x1 = (Nat.add x2 (S y0)))).
Definition term70 (x0 : real) := real_mul x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term17 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_lt x0 y1) /\ ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y2)))) -> real_lt (real_mul x0 y0) (real_mul y1 y2)) x1.
Definition term3 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_lt x0 y0) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y2)))) -> real_lt (real_mul x0 y1) (real_mul y0 y2)) x1.
Definition term148 (x0 : real) (x1 : nat) := real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S x1)).
Definition term101 (x0 : nat) (x1 : real) (x2 : nat) := @eq Prop ((fun y0 : nat => real_lt (real_pow x1 x0) (real_pow x1 y0)) x2).
Definition term197 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_of_num x1).
Definition term205 (x0 : nat) (x1 : real) (x2 : nat) := (real_lt (real_of_num (NUMERAL 0)) (real_pow x1 x0)) /\ (real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x1 (S x2))).
Definition term184 := (forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1)))))).
Definition term183 := (forall y0 : nat, (Peano.le (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.le 0 (BIT0 y0)) = True) /\ ((forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1))))))).
Definition term117 := (forall y0 : nat, (Peano.lt (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt 0 (BIT0 y0)) = (Peano.lt 0 y0)) /\ ((forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1))))))).
Definition term116 := (forall y0 : nat, (Peano.lt (BIT0 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt (BIT1 y0) 0) = False) /\ ((forall y0 : nat, (Peano.lt 0 (BIT0 y0)) = (Peano.lt 0 y0)) /\ ((forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1)))))))).
Definition term198 := real_le (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term170 (x0 : real) := real_lt (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 (real_pow x0 (NUMERAL 0))).
Definition term158 (x0 : real) := forall y0 : nat, (real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y0))) -> real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S (S y0))).
Definition term39 (x0 : real) (x1 : real) := fun y0 : real => (real_lt x0 y0) /\ (real_lt y0 x1).
Definition term53 (x0 : real) (x1 : nat) := (forall y0 : real, forall y1 : nat, (real_lt (real_of_num (NUMERAL 0)) y0) -> real_lt (real_of_num (NUMERAL 0)) (real_pow y0 y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_pow x0 x1).
Definition term167 (x0 : real) := real_pow x0 (S (NUMERAL 0)).
Definition term93 (x0 : nat) (x1 : real) (x2 : nat) := ((real_lt (real_of_num (NUMERAL (BIT1 0))) x1) /\ (Peano.lt x0 x2)) -> real_lt (real_pow x1 x0) (real_pow x1 x2).
Definition term152 (x0 : real) (x1 : nat) := real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S (S x1))).
Definition term174 (x0 : real) := (fun y0 : real => (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0) x0.
Definition term85 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 (S y1)))) x1.
Definition term172 (x0 : real) (x1 : nat) := real_mul x0 (real_pow x0 (S x1)).
Definition term163 (x0 : real) := fun y0 : nat => (fun y1 : nat => real_lt (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (S y1))) y0.
Definition term105 (x0 : real) (x1 : nat) := real_lt (real_pow x0 x1).
Definition term135 := Peano.lt 0 (BIT1 0).
Definition term35 (x0 : real) (x1 : real) (x2 : real) := ((real_lt x1 x0) /\ (real_lt x0 x2)) -> real_lt x1 x2.
Definition term68 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_lt y0 y2)) -> real_lt (real_mul y1 y0) (real_mul y1 y2)) x0.
Definition term56 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y1 y2)) -> real_lt (real_mul y0 y1) (real_mul y0 y2)) x0.
Definition term30 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_lt y0 y1) /\ (real_lt y1 y2)) -> real_lt y0 y2) x0.
Definition term16 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_lt y0 y2) /\ ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_lt y1 y3)))) -> real_lt (real_mul y0 y1) (real_mul y2 y3)) x0.
Definition term1 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_lt y0 y1) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt y2 y3)))) -> real_lt (real_mul y0 y2) (real_mul y1 y3)) x0.
Definition term95 (x0 : real) := real_lt (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term185 := (forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT0 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.le (BIT1 y0) (BIT1 y1)) = (Peano.le y0 y1))))).
Definition term119 := (forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT0 y0) (BIT1 y1)) = (Peano.le y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT0 y1)) = (Peano.lt y0 y1)) /\ (forall y0 : nat, forall y1 : nat, (Peano.lt (BIT1 y0) (BIT1 y1)) = (Peano.lt y0 y1))))).
Definition term134 := NUMERAL (BIT1 0).
Definition term74 := forall y0 : real, y0 = (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))).
Definition term72 := fun y0 : real => y0 = (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))).
Definition term186 := forall y0 : nat, (Peano.le 0 (BIT1 y0)) = True.
Definition term120 := forall y0 : nat, (Peano.lt 0 (BIT1 y0)) = True.
Definition term102 (x0 : nat) (x1 : real) (x2 : nat) := @eq Prop (real_lt (real_pow x1 x0) (real_pow x1 x2)).
Definition term11 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (forall y0 : real, forall y1 : real, forall y2 : real, forall y3 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_lt y0 y1) /\ ((real_le (real_of_num (NUMERAL 0)) y2) /\ (real_lt y2 y3)))) -> real_lt (real_mul y0 y2) (real_mul y1 y3)) -> real_lt (real_mul x0 x1) (real_mul x2 x3).
