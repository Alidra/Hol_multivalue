Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term188 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term155 (x0 : nat) := real_div (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term133 (x0 : real -> Prop) := ~ (all x0).
Definition term173 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term142 := exists y0 : real, ~ (y0 = (real_add (real_mul (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow y0 (NUMERAL (BIT1 0)))))).
Definition term162 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term205 (x0 : real) := real_gt (real_sub x0 (real_add (real_mul (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (NUMERAL (BIT1 0)))))).
Definition term179 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term48 (x0 : real) := @eq real ((fun y0 : real => y0) x0).
Definition term180 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term107 := (fun y0 : nat => (fun y1 : nat => @COND real (y1 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y0) (S (NUMERAL 0)).
Definition term102 (x0 : real) := (fun y0 : nat => (fun y1 : nat => real_mul ((fun y2 : nat => @COND real (y2 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y1) (real_pow x0 y1)) y0) (S (NUMERAL 0)).
Definition term154 (x0 : nat) := real_neg (real_of_num x0).
Definition term118 := @COND real True (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term72 := real_of_num (NUMERAL 0).
Definition term85 (x0 : nat) := @COND real (x0 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term1 := ((0 = 0) = True) /\ ((forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))))).
Definition term0 := (forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1)) /\ (((0 = 0) = True) /\ ((forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))))))).
Definition term219 (x0 : real) := (fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0.
Definition term4 := (forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))).
Definition term2 := (forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))))).
Definition term122 (x0 : real) := real_pow x0 (NUMERAL (BIT1 0)).
Definition term168 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term110 := @eq real ((fun y0 : nat => @COND real (y0 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) (S (NUMERAL 0))).
Definition term182 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term128 (x0 : real) := @COND real True (real_add (real_mul (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (NUMERAL (BIT1 0))))) (real_mul (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL 0))).
Definition term239 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term213 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term139 (x0 : real) := ~ (x0 = (real_add (real_mul (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (NUMERAL (BIT1 0)))))).
Definition term24 (x0 : nat) := NUMERAL (S x0).
Definition term65 := S (NUMERAL 0).
Definition term29 (x0 : nat) (x1 : nat -> real) := forall y0 : nat, (@sum nat (dotdot x0 (S y0)) x1) = (@COND real (Peano.le x0 (S y0)) (real_add (@sum nat (dotdot x0 y0) x1) (x1 (S y0))) (@sum nat (dotdot x0 y0) x1)).
Definition term196 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term130 := fun y0 : real => y0 = (real_add (real_mul (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow y0 (NUMERAL (BIT1 0))))).
Definition term8 := (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)).
Definition term135 := ~ (forall y0 : real, y0 = (real_add (real_mul (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow y0 (NUMERAL (BIT1 0)))))).
Definition term44 (x0 : real) := (fun y0 : real => (fun y1 : real => y1) y0) x0.
Definition term157 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term37 (x0 : real -> real) := (fun y0 : real -> real => (polynomial_function y0) = (exists y1 : nat, exists y2 : nat -> real, forall y3 : real, (y0 y3) = (@sum nat (dotdot (NUMERAL 0) y1) (fun y4 : nat => real_mul (y2 y4) (real_pow y3 y4))))) x0.
Definition term131 := forall y0 : real, y0 = (@sum nat (dotdot (NUMERAL 0) (S (NUMERAL 0))) (fun y1 : nat => real_mul ((fun y2 : nat => @COND real (y2 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y1) (real_pow y0 y1))).
Definition term53 (x0 : nat) (x1 : nat -> real) := forall y0 : real, y0 = (@sum nat (dotdot (NUMERAL 0) x0) (fun y1 : nat => real_mul (x1 y1) (real_pow y0 y1))).
Definition term17 (x0 : nat) := forall y0 : nat, ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0).
Definition term11 (x0 : nat) := forall y0 : nat, ((BIT1 x0) = (BIT1 y0)) = (x0 = y0).
Definition term81 := (fun y0 : nat => (fun y1 : nat => @COND real (y1 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y0) (NUMERAL 0).
Definition term74 (x0 : real) := (fun y0 : nat => (fun y1 : nat => real_mul ((fun y2 : nat => @COND real (y2 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y1) (real_pow x0 y1)) y0) (NUMERAL 0).
Definition term67 (x0 : real) := @sum nat (dotdot (NUMERAL 0) (NUMERAL 0)) (fun y0 : nat => real_mul ((fun y1 : nat => @COND real (y1 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y0) (real_pow x0 y0)).
Definition term141 := fun y0 : real => ~ (y0 = (real_add (real_mul (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow y0 (NUMERAL (BIT1 0)))))).
Definition term191 := real_neg (real_of_num (NUMERAL 0)).
Definition term32 (x0 : nat) (x1 : nat) (x2 : nat -> real) := @COND real (Peano.le x0 (S x1)) (real_add (@sum nat (dotdot x0 x1) x2) (x2 (S x1))) (@sum nat (dotdot x0 x1) x2).
Definition term80 (x0 : real) := real_mul ((fun y0 : nat => @COND real (y0 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) (NUMERAL 0)) (real_pow x0 (NUMERAL 0)).
Definition term166 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term161 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term83 := fun y0 : nat => @COND real (y0 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term186 := real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term25 (x0 : nat) := (fun y0 : nat => Peano.le (NUMERAL 0) y0) x0.
Definition term178 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term20 := ((S 0) = (BIT1 0)) /\ ((forall y0 : nat, (S (BIT0 y0)) = (BIT1 y0)) /\ (forall y0 : nat, (S (BIT1 y0)) = (BIT0 (S y0)))).
Definition term156 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term13 := forall y0 : nat, (0 = (BIT1 y0)) = False.
Definition term98 (x0 : real) := real_pow x0 (NUMERAL 0).
Definition term164 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term243 := ((~ (forall y0 : real, y0 = (real_add (real_mul (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow y0 (NUMERAL (BIT1 0))))))) -> False) -> forall y0 : real, y0 = (real_add (real_mul (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow y0 (NUMERAL (BIT1 0))))).
Definition term23 (x0 : nat) := S (NUMERAL x0).
Definition term96 := real_mul ((fun y0 : nat => @COND real (y0 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) (NUMERAL 0)).
Definition term232 (x0 : Prop) := exists y0 : real, x0.
Definition term226 := exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0.
Definition term197 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term22 (x0 : nat) := (fun y0 : nat => (S (NUMERAL y0)) = (NUMERAL (S y0))) x0.
Definition term244 := exists y0 : nat -> real, forall y1 : real, y1 = (@sum nat (dotdot (NUMERAL 0) (S (NUMERAL 0))) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2))).
Definition term57 (x0 : nat) := exists y0 : nat -> real, forall y1 : real, y1 = (@sum nat (dotdot (NUMERAL 0) x0) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2))).
Definition term56 (x0 : nat) := exists y0 : nat -> real, forall y1 : real, ((fun y2 : real => y2) y1) = (@sum nat (dotdot (NUMERAL 0) x0) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2))).
Definition term123 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (NUMERAL (BIT1 0))).
Definition term62 (x0 : real) := @COND real (Peano.le (NUMERAL 0) (S (NUMERAL 0))) (real_add (@sum nat (dotdot (NUMERAL 0) (NUMERAL 0)) (fun y0 : nat => real_mul ((fun y1 : nat => @COND real (y1 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y0) (real_pow x0 y0))) ((fun y0 : nat => real_mul ((fun y1 : nat => @COND real (y1 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y0) (real_pow x0 y0)) (S (NUMERAL 0)))) (@sum nat (dotdot (NUMERAL 0) (NUMERAL 0)) (fun y0 : nat => real_mul ((fun y1 : nat => @COND real (y1 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y0) (real_pow x0 y0))).
Definition term195 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term228 := or (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term201 (x0 : real) := real_gt (real_neg (real_sub x0 (real_add (real_mul (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (NUMERAL (BIT1 0))))))).
Definition term167 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term160 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term28 (x0 : nat -> real) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (@sum nat (dotdot y0 (S y1)) x0) = (@COND real (Peano.le y0 (S y1)) (real_add (@sum nat (dotdot y0 y1) x0) (x0 (S y1))) (@sum nat (dotdot y0 y1) x0))) x1.
Definition term6 := (forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))).
Definition term103 (x0 : real) := (fun y0 : nat => real_mul ((fun y1 : nat => @COND real (y1 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y0) (real_pow x0 y0)) (S (NUMERAL 0)).
Definition term100 (x0 : real) := real_add (@sum nat (dotdot (NUMERAL 0) (NUMERAL 0)) (fun y0 : nat => real_mul ((fun y1 : nat => @COND real (y1 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y0) (real_pow x0 y0))).
Definition term41 := fun y0 : real => y0.
Definition term136 := exists y0 : real, ~ ((fun y1 : real => y1 = (real_add (real_mul (real_of_num (NUMERAL 0)) (real_pow y1 (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow y1 (NUMERAL (BIT1 0)))))) y0).
Definition term101 (x0 : real) := real_add (real_mul (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL 0))).
Definition term234 := real_lt (real_of_num (NUMERAL 0)).
Definition term95 := @COND real False (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term39 := polynomial_function (fun y0 : real => y0).
Definition term7 := (forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))).
Definition term145 := real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term113 := @eq nat (S (NUMERAL 0)).
Definition term181 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term174 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term137 (x0 : real) := (fun y0 : real => y0 = (real_add (real_mul (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow y0 (NUMERAL (BIT1 0)))))) x0.
Definition term209 := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term69 (a0 : Type') (a1 : Type') (x0 : a1) (x1 : a0) (x2 : a0) := @COND a0 (x0 = x0) x1 x2.
Definition term14 (x0 : nat) := (fun y0 : nat => (0 = (BIT1 y0)) = False) x0.
Definition term112 := NUMERAL (S 0).
Definition term158 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term143 (x0 : real) := (real_gt (real_sub x0 (real_add (real_mul (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub x0 (real_add (real_mul (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (NUMERAL (BIT1 0))))))) (real_of_num (NUMERAL 0))).
Definition term214 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term230 := (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term241 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term192 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term115 := @COND real ((S (NUMERAL 0)) = (NUMERAL (BIT1 0))).
Definition term84 (x0 : nat) := (fun y0 : nat => @COND real (y0 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) x0.
Definition term163 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term127 (x0 : real) := @COND real True (real_add (real_mul (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (NUMERAL (BIT1 0))))).
Definition term66 := @COND real (Peano.le (NUMERAL 0) (S (NUMERAL 0))).
Definition term77 (x0 : real) := fun y0 : nat => (fun y1 : nat => real_mul ((fun y2 : nat => @COND real (y2 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y1) (real_pow x0 y1)) y0.
Definition term33 (x0 : nat -> real) := forall y0 : nat, (@sum nat (dotdot y0 (NUMERAL 0)) x0) = (@COND real (y0 = (NUMERAL 0)) (x0 (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term42 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term215 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term204 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term236 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term218 := fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term27 (x0 : nat -> real) := forall y0 : nat, forall y1 : nat, (@sum nat (dotdot y0 (S y1)) x0) = (@COND real (Peano.le y0 (S y1)) (real_add (@sum nat (dotdot y0 y1) x0) (x0 (S y1))) (@sum nat (dotdot y0 y1) x0)).
Definition term15 := forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1).
Definition term9 := forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1).
Definition term35 (x0 : nat) (x1 : nat -> real) := @sum nat (dotdot x0 (NUMERAL 0)) x1.
Definition term144 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term175 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term31 (x0 : nat) (x1 : nat) (x2 : nat -> real) := @sum nat (dotdot x0 (S x1)) x2.
Definition term73 (x0 : nat -> real) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term106 (x0 : real) := real_mul ((fun y0 : nat => @COND real (y0 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) (S (NUMERAL 0))) (real_pow x0 (S (NUMERAL 0))).
Definition term43 (x0 : real -> real) (x1 : real) := (fun y0 : real => x0 y0) x1.
Definition term224 := @eq Prop (exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term223 := @eq Prop (exists y0 : real, ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0)).
Definition term99 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL 0)).
Definition term117 := @COND real True (real_of_num (NUMERAL (BIT1 0))).
Definition term134 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term75 (x0 : real) (x1 : nat) := (fun y0 : nat => real_mul ((fun y1 : nat => @COND real (y1 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y0) (real_pow x0 y0)) x1.
Definition term200 (x0 : real) := @eq real (real_neg (real_sub x0 (real_add (real_mul (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (NUMERAL (BIT1 0))))))).
Definition term76 (x0 : real) (x1 : nat) := real_mul ((fun y0 : nat => @COND real (y0 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) x1) (real_pow x0 x1).
Definition term171 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term68 (x0 : real) := @COND real ((NUMERAL 0) = (NUMERAL 0)) ((fun y0 : nat => real_mul ((fun y1 : nat => @COND real (y1 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y0) (real_pow x0 y0)) (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term88 := @eq real ((fun y0 : nat => @COND real (y0 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) (NUMERAL 0)).
Definition term79 (x0 : real) := @eq real ((fun y0 : nat => real_mul ((fun y1 : nat => @COND real (y1 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y0) (real_pow x0 y0)) (NUMERAL 0)).
Definition term59 := fun y0 : nat => exists y1 : nat -> real, forall y2 : real, y2 = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3))).
Definition term58 := fun y0 : nat => exists y1 : nat -> real, forall y2 : real, ((fun y3 : real => y3) y2) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3))).
Definition term238 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term26 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term207 (x0 : real) := or (real_gt (real_sub x0 (real_add (real_mul (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term165 := S (Nat.add 0 0).
Definition term63 (x0 : real) := fun y0 : nat => real_mul ((fun y1 : nat => @COND real (y1 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y0) (real_pow x0 y0).
Definition term193 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term150 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term151 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term242 := (~ (forall y0 : real, y0 = (real_add (real_mul (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow y0 (NUMERAL (BIT1 0))))))) -> False.
Definition term177 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term91 := @COND real ((NUMERAL 0) = (NUMERAL (BIT1 0))).
Definition term47 (x0 : real) := @eq real ((fun y0 : real => (fun y1 : real => y1) y0) x0).
Definition term97 := real_mul (real_of_num (NUMERAL 0)).
Definition term233 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term231 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term169 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term34 (x0 : nat -> real) (x1 : nat) := (fun y0 : nat => (@sum nat (dotdot y0 (NUMERAL 0)) x0) = (@COND real (y0 = (NUMERAL 0)) (x0 (NUMERAL 0)) (real_of_num (NUMERAL 0)))) x1.
Definition term120 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term222 := fun y0 : real => ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term185 := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term153 := real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term45 (x0 : real) := (fun y0 : real => y0) x0.
Definition term216 := exists y0 : real, ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term210 := fun y0 : real => (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term126 (x0 : real) := @COND real (Peano.le (NUMERAL 0) (S (NUMERAL 0))) (real_add (@sum nat (dotdot (NUMERAL 0) (NUMERAL 0)) (fun y0 : nat => real_mul ((fun y1 : nat => @COND real (y1 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y0) (real_pow x0 y0))) ((fun y0 : nat => real_mul ((fun y1 : nat => @COND real (y1 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y0) (real_pow x0 y0)) (S (NUMERAL 0)))).
Definition term176 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term114 := @eq nat (NUMERAL (BIT1 0)).
Definition term93 := @COND real ((NUMERAL 0) = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term16 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1)) x0.
Definition term10 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)) x0.
Definition term221 (x0 : real) := ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0) \/ ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0).
Definition term21 := forall y0 : nat, (S (NUMERAL y0)) = (NUMERAL (S y0)).
Definition term148 (x0 : real) := real_sub x0 (real_add (real_mul (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (NUMERAL (BIT1 0))))).
Definition term198 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term46 := fun y0 : real => (fun y1 : real => y1) y0.
Definition term129 := fun y0 : real => y0 = (@sum nat (dotdot (NUMERAL 0) (S (NUMERAL 0))) (fun y1 : nat => real_mul ((fun y2 : nat => @COND real (y2 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y1) (real_pow y0 y1))).
Definition term172 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term187 (x0 : real) := real_div x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term147 (x0 : real) := real_add (real_of_num (NUMERAL 0)) x0.
Definition term184 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term92 := real_of_num (NUMERAL (BIT1 0)).
Definition term132 := forall y0 : real, y0 = (real_add (real_mul (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow y0 (NUMERAL (BIT1 0))))).
Definition term94 := @COND real False (real_of_num (NUMERAL (BIT1 0))).
Definition term86 := fun y0 : nat => (fun y1 : nat => @COND real (y1 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y0.
Definition term108 := (fun y0 : nat => @COND real (y0 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) (S (NUMERAL 0)).
Definition term111 := @COND real ((S (NUMERAL 0)) = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term89 := @COND real ((NUMERAL 0) = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term225 := fun y0 : real => (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0.
Definition term87 := @eq real ((fun y0 : nat => (fun y1 : nat => @COND real (y1 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y0) (NUMERAL 0)).
Definition term78 (x0 : real) := @eq real ((fun y0 : nat => (fun y1 : nat => real_mul ((fun y2 : nat => @COND real (y2 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y1) (real_pow x0 y1)) y0) (NUMERAL 0)).
Definition term119 := real_mul ((fun y0 : nat => @COND real (y0 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) (S (NUMERAL 0))).
Definition term189 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term71 (x0 : real) := (fun y0 : nat => real_mul ((fun y1 : nat => @COND real (y1 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y0) (real_pow x0 y0)) (NUMERAL 0).
Definition term125 (x0 : real) := real_add (real_mul (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (NUMERAL (BIT1 0)))).
Definition term138 (x0 : real) := ~ ((fun y0 : real => y0 = (real_add (real_mul (real_of_num (NUMERAL 0)) (real_pow y0 (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow y0 (NUMERAL (BIT1 0)))))) x0).
Definition term30 (x0 : nat) (x1 : nat -> real) (x2 : nat) := (fun y0 : nat => (@sum nat (dotdot x0 (S y0)) x1) = (@COND real (Peano.le x0 (S y0)) (real_add (@sum nat (dotdot x0 y0) x1) (x1 (S y0))) (@sum nat (dotdot x0 y0) x1))) x2.
Definition term140 := fun y0 : real => ~ ((fun y1 : real => y1 = (real_add (real_mul (real_of_num (NUMERAL 0)) (real_pow y1 (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow y1 (NUMERAL (BIT1 0)))))) y0).
Definition term70 (x0 : nat) (x1 : real) (x2 : real) := @COND real (x0 = x0) x1 x2.
Definition term237 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term116 := @COND real ((S (NUMERAL 0)) = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term208 := or (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term105 (x0 : real) := @eq real ((fun y0 : nat => real_mul ((fun y1 : nat => @COND real (y1 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y0) (real_pow x0 y0)) (S (NUMERAL 0))).
Definition term170 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term220 (x0 : real) := or ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0).
Definition term60 := exists y0 : nat, exists y1 : nat -> real, forall y2 : real, y2 = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3))).
Definition term40 := exists y0 : nat, exists y1 : nat -> real, forall y2 : real, ((fun y3 : real => y3) y2) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3))).
Definition term38 (x0 : real -> real) := exists y0 : nat, exists y1 : nat -> real, forall y2 : real, (x0 y2) = (@sum nat (dotdot (NUMERAL 0) y0) (fun y3 : nat => real_mul (y1 y3) (real_pow y2 y3))).
Definition term190 (x0 : real) := real_neg (real_sub x0 (real_add (real_mul (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (NUMERAL (BIT1 0)))))).
Definition term3 := (forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))).
Definition term203 (x0 : real) := real_gt (real_neg (real_sub x0 (real_add (real_mul (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (NUMERAL (BIT1 0))))))) (real_of_num (NUMERAL 0)).
Definition term19 := (forall y0 : nat, (S (NUMERAL y0)) = (NUMERAL (S y0))) /\ (((S 0) = (BIT1 0)) /\ ((forall y0 : nat, (S (BIT0 y0)) = (BIT1 y0)) /\ (forall y0 : nat, (S (BIT1 y0)) = (BIT0 (S y0))))).
Definition term64 := Peano.le (NUMERAL 0) (S (NUMERAL 0)).
Definition term124 (x0 : real) := real_add (@sum nat (dotdot (NUMERAL 0) (NUMERAL 0)) (fun y0 : nat => real_mul ((fun y1 : nat => @COND real (y1 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y0) (real_pow x0 y0))) ((fun y0 : nat => real_mul ((fun y1 : nat => @COND real (y1 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y0) (real_pow x0 y0)) (S (NUMERAL 0))).
Definition term61 (x0 : real) := @sum nat (dotdot (NUMERAL 0) (S (NUMERAL 0))) (fun y0 : nat => real_mul ((fun y1 : nat => @COND real (y1 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y0) (real_pow x0 y0)).
Definition term121 (x0 : real) := real_pow x0 (S (NUMERAL 0)).
Definition term49 (x0 : nat) (x1 : nat -> real) (x2 : real) := @sum nat (dotdot (NUMERAL 0) x0) (fun y0 : nat => real_mul (x1 y0) (real_pow x2 y0)).
Definition term82 := (fun y0 : nat => @COND real (y0 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) (NUMERAL 0).
Definition term245 := fun y0 : nat -> real => forall y1 : real, y1 = (@sum nat (dotdot (NUMERAL 0) (S (NUMERAL 0))) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2))).
Definition term55 (x0 : nat) := fun y0 : nat -> real => forall y1 : real, y1 = (@sum nat (dotdot (NUMERAL 0) x0) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2))).
Definition term54 (x0 : nat) := fun y0 : nat -> real => forall y1 : real, ((fun y2 : real => y2) y1) = (@sum nat (dotdot (NUMERAL 0) x0) (fun y2 : nat => real_mul (y0 y2) (real_pow y1 y2))).
Definition term36 (x0 : nat) (x1 : nat -> real) := @COND real (x0 = (NUMERAL 0)) (x1 (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term235 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term159 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term152 (x0 : nat) := real_div (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term194 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term18 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0)) x1.
Definition term12 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((BIT1 x0) = (BIT1 y0)) = (x0 = y0)) x1.
Definition term199 := real_div (real_of_num (NUMERAL 0)).
Definition term146 := real_add (real_of_num (NUMERAL 0)).
Definition term229 := or (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term212 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term52 (x0 : nat) (x1 : nat -> real) := forall y0 : real, ((fun y1 : real => y1) y0) = (@sum nat (dotdot (NUMERAL 0) x0) (fun y1 : nat => real_mul (x1 y1) (real_pow y0 y1))).
Definition term183 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term206 (x0 : real) := real_gt (real_sub x0 (real_add (real_mul (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term109 := @eq real ((fun y0 : nat => (fun y1 : nat => @COND real (y1 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y0) (S (NUMERAL 0))).
Definition term104 (x0 : real) := @eq real ((fun y0 : nat => (fun y1 : nat => real_mul ((fun y2 : nat => @COND real (y2 = (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) y1) (real_pow x0 y1)) y0) (S (NUMERAL 0))).
Definition term5 := (forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))).
Definition term90 := NUMERAL (BIT1 0).
Definition term217 := (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term211 := exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term51 (x0 : nat) (x1 : nat -> real) := fun y0 : real => y0 = (@sum nat (dotdot (NUMERAL 0) x0) (fun y1 : nat => real_mul (x1 y1) (real_pow y0 y1))).
Definition term149 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term227 := exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term50 (x0 : nat) (x1 : nat -> real) := fun y0 : real => ((fun y1 : real => y1) y0) = (@sum nat (dotdot (NUMERAL 0) x0) (fun y1 : nat => real_mul (x1 y1) (real_pow y0 y1))).
Definition term240 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term202 := real_gt (real_of_num (NUMERAL 0)).
