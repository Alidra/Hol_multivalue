Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term264 (x0 : nat) (x1 : nat) (x2 : nat) := @IN nat x0 (dotdot x1 x2).
Definition term70 (x0 : int) (x1 : int) := real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term219 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term246 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term177 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term2 (x0 : nat) := Peano.le (NUMERAL (BIT1 0)) x0.
Definition term85 (x0 : nat) := real_div (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term97 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term278 := fun y0 : nat -> Prop => y0 (@ε nat y0).
Definition term148 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term214 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term156 := real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term109 (x0 : int) := real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term215 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term84 (x0 : nat) := real_neg (real_of_num x0).
Definition term232 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term45 := real_of_int (int_of_num (NUMERAL 0)).
Definition term77 (x0 : Prop) := ~ (~ x0).
Definition term46 := real_of_num (NUMERAL 0).
Definition term259 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (@IN nat y2 (dotdot y0 y1)) = ((Peano.le y0 y2) /\ (Peano.le y2 y1))) x0.
Definition term125 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))).
Definition term283 (a0 : Type') (a1 : Type') (x0 : nat) := @dest_finite_sum a0 a1 (@mk_finite_sum a0 a1 x0).
Definition term39 (x0 : int) (x1 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x1) -> (~ (int_le (int_of_num (NUMERAL (BIT1 0))) x0)) \/ (int_le (int_of_num (NUMERAL (BIT1 0))) (int_add x0 x1))).
Definition term164 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term43 := int_of_num (NUMERAL 0).
Definition term252 (x0 : int) (x1 : int) := ((~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ ((real_le (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) /\ (real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))))))) -> False) -> ~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ ((real_le (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) /\ (real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))))).
Definition term213 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term154 := ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term217 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term158 := real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term140 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term68 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))).
Definition term141 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term242 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term224 (x0 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))).
Definition term19 (x0 : int) (x1 : int) := ~ (~ ((int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x1) -> (~ (int_le (int_of_num (NUMERAL (BIT1 0))) x0)) \/ (int_le (int_of_num (NUMERAL (BIT1 0))) (int_add x0 x1)))).
Definition term40 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> (~ (int_le (int_of_num (NUMERAL (BIT1 0))) x0)) \/ (int_le (int_of_num (NUMERAL (BIT1 0))) (int_add x0 x1)).
Definition term92 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term113 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term3 (x0 : nat) (x1 : nat) := Peano.le (NUMERAL (BIT1 0)) (Nat.add x0 x1).
Definition term206 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term197 (x0 : int) (x1 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))).
Definition term196 (x0 : int) (x1 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))).
Definition term123 (x0 : int) := real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term107 (x0 : int) := real_ge (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term157 (x0 : nat) := real_add (real_of_num x0) (real_neg (real_of_num x0)).
Definition term14 := int_le (int_of_num (NUMERAL (BIT1 0))).
Definition term272 (a0 : Type') (a1 : Type') := (Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0))) -> (Peano.le (NUMERAL (BIT1 0)) (Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1)))) = True.
Definition term247 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_neg (real_of_num x1)).
Definition term270 := and (Peano.le (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term211 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term210 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term152 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term147 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term134 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term83 := real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term73 (x0 : int) (x1 : int) := (real_le (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) /\ (real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term49 (x0 : int) := real_le (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term182 (x0 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term7 (x0 : nat) := ~ (Peano.le (NUMERAL (BIT1 0)) x0).
Definition term106 (x0 : int) := real_ge (real_of_int x0).
Definition term16 (x0 : nat) (x1 : nat) := (~ (int_le (int_of_num (NUMERAL (BIT1 0))) (int_of_num x0))) \/ (int_le (int_of_num (NUMERAL (BIT1 0))) (int_add (int_of_num x0) (int_of_num x1))).
Definition term255 (x0 : nat) (x1 : nat) := (int_le (int_of_num (NUMERAL 0)) (int_of_num x1)) -> (~ (int_le (int_of_num (NUMERAL (BIT1 0))) (int_of_num x0))) \/ (int_le (int_of_num (NUMERAL (BIT1 0))) (int_add (int_of_num x0) (int_of_num x1))).
Definition term117 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term57 (x0 : int) (x1 : int) := ~ (int_le x0 x1).
Definition term195 (x0 : int) (x1 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))) (real_of_num (NUMERAL 0)).
Definition term87 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term8 (x0 : nat) := ~ (int_le (int_of_num (NUMERAL (BIT1 0))) (int_of_num x0)).
Definition term64 (x0 : int) (x1 : int) := real_of_int (int_add (int_add x0 x1) (int_of_num (NUMERAL (BIT1 0)))).
Definition term240 := real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term137 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term0 (x0 : nat) (x1 : nat) := (Peano.le (NUMERAL (BIT1 0)) x0) -> Peano.le (NUMERAL (BIT1 0)) (Nat.add x0 x1).
Definition term135 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term60 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_add x0 x1) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term34 (x0 : int) (x1 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) x1) -> (~ (int_le (int_of_num (NUMERAL (BIT1 0))) x0)) \/ (int_le (int_of_num (NUMERAL (BIT1 0))) (int_add x0 x1))).
Definition term105 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term29 (x0 : int) := ~ (int_le (int_of_num (NUMERAL (BIT1 0))) x0).
Definition term150 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term276 (a0 : Type') (a1 : Type') := fun y0 : nat => @IN nat y0 (dotdot (NUMERAL (BIT1 0)) (Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1)))).
Definition term202 (x0 : int) (x1 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_int x1).
Definition term131 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term99 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term241 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term171 (x0 : int) := and (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term56 (x0 : int) := real_le (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0).
Definition term287 (a0 : Type') (a1 : Type') := forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))) = ((@dest_finite_sum a0 a1 (@mk_finite_sum a0 a1 y0)) = y0).
Definition term167 (x0 : int) (x1 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))).
Definition term273 (a0 : Type') := Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 (@UNIV a0)).
Definition term91 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term245 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term21 (x0 : int) := ~ (~ (int_le (int_of_num (NUMERAL (BIT1 0))) x0)).
Definition term173 (x0 : int) (x1 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))))).
Definition term212 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term153 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term209 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term122 (x0 : int) := real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term104 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term261 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (@IN nat y1 (dotdot x0 y0)) = ((Peano.le x0 y1) /\ (Peano.le y1 y0))) x1.
Definition term198 (x0 : int) (x1 : int) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x1) (real_of_num (NUMERAL 0))).
Definition term48 := real_le (real_of_num (NUMERAL 0)).
Definition term62 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term248 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term169 (x0 : int) := and (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term186 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term130 (x0 : int) (x1 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term175 := real_lt (real_of_num (NUMERAL 0)).
Definition term128 (x0 : int) (x1 : int) := real_sub (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term67 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_of_int x1)).
Definition term103 (x0 : int) := real_add (real_of_int x0).
Definition term17 (x0 : nat) := (fun y0 : nat => int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) x0.
Definition term256 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 y0)) x0.
Definition term23 (x0 : int) (x1 : int) := ~ (int_le (int_of_num (NUMERAL (BIT1 0))) (int_add x0 x1)).
Definition term268 (a0 : Type') (a1 : Type') := Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1)).
Definition term229 (x0 : int) := (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))).
Definition term78 (x0 : int) (x1 : int) := ~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ ((real_le (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) /\ (real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))))))).
Definition term193 (x0 : int) (x1 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))).
Definition term231 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term250 := and ((NUMERAL 0) = (NUMERAL 0)).
Definition term9 (x0 : nat) := or (~ (Peano.le (NUMERAL (BIT1 0)) x0)).
Definition term126 := real_sub (real_of_num (NUMERAL (BIT1 0))).
Definition term258 (x0 : nat) := (fun y0 : nat => Peano.le y0 y0) x0.
Definition term205 (x0 : int) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term22 (x0 : int) := int_le (int_of_num (NUMERAL (BIT1 0))) x0.
Definition term44 (x0 : nat) := real_of_int (int_of_num x0).
Definition term271 (x0 : nat) (x1 : nat) := (Peano.le (NUMERAL (BIT1 0)) x0) -> (Peano.le (NUMERAL (BIT1 0)) (Nat.add x0 x1)) = True.
Definition term38 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ ((int_le (int_of_num (NUMERAL 0)) x1) /\ ((int_le (int_of_num (NUMERAL (BIT1 0))) x0) /\ (~ (int_le (int_of_num (NUMERAL (BIT1 0))) (int_add x0 x1))))).
Definition term161 := real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term216 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term98 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term58 (x0 : int) (x1 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1.
Definition term127 (x0 : int) (x1 : int) := real_sub (real_of_num (NUMERAL (BIT1 0))) (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term63 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term207 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term90 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term249 := ((NUMERAL 0) = (NUMERAL 0)) /\ ((NUMERAL (BIT1 0)) = (NUMERAL 0)).
Definition term118 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term26 (x0 : int) (x1 : int) := (~ (~ (int_le (int_of_num (NUMERAL (BIT1 0))) x0))) /\ (~ (int_le (int_of_num (NUMERAL (BIT1 0))) (int_add x0 x1))).
Definition term59 (x0 : int) (x1 : int) := int_le (int_add (int_add x0 x1) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL (BIT1 0))).
Definition term277 (a0 : Type') := fun y0 : a0 -> Prop => y0 (@ε a0 y0).
Definition term289 (a0 : Type') (a1 : Type') := (forall y0 : finite_sum a0 a1, (@mk_finite_sum a0 a1 (@dest_finite_sum a0 a1 y0)) = y0) /\ (forall y0 : nat, (@IN nat y0 (dotdot (NUMERAL (BIT1 0)) (Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))) = ((@dest_finite_sum a0 a1 (@mk_finite_sum a0 a1 y0)) = y0)).
Definition term172 (x0 : int) (x1 : int) := (real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0)))).
Definition term149 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term280 (a0 : Type') (a1 : Type') := (fun y0 : nat => @IN nat y0 (dotdot (NUMERAL (BIT1 0)) (Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))) (@ε nat (fun y0 : nat => @IN nat y0 (dotdot (NUMERAL (BIT1 0)) (Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1)))))).
Definition term143 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term204 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0).
Definition term129 (x0 : int) (x1 : int) := real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))))).
Definition term10 (x0 : nat) := or (~ (int_le (int_of_num (NUMERAL (BIT1 0))) (int_of_num x0))).
Definition term260 (x0 : nat) := forall y0 : nat, forall y1 : nat, (@IN nat y1 (dotdot x0 y0)) = ((Peano.le x0 y1) /\ (Peano.le y1 y0)).
Definition term274 (a0 : Type') (a1 : Type') := Peano.le (NUMERAL (BIT1 0)) (Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))).
Definition term168 (x0 : int) (x1 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0)).
Definition term279 (a0 : Type') (a1 : Type') := (fun y0 : nat -> Prop => y0 (@ε nat y0)) (fun y0 : nat => @IN nat y0 (dotdot (NUMERAL (BIT1 0)) (Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))).
Definition term115 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term139 (x0 : int) (x1 : int) := real_add (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term223 (x0 : int) := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term190 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term27 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL (BIT1 0))) x0) /\ (~ (int_le (int_of_num (NUMERAL (BIT1 0))) (int_add x0 x1))).
Definition term281 (a0 : Type') (a1 : Type') (x0 : finite_sum a0 a1) := @mk_finite_sum a0 a1 (@dest_finite_sum a0 a1 x0).
Definition term199 (x0 : real) (x1 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term183 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term5 (x0 : nat) := int_le (int_of_num (NUMERAL (BIT1 0))) (int_of_num x0).
Definition term54 := real_le (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term119 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term30 (x0 : int) (x1 : int) := int_le (int_of_num (NUMERAL (BIT1 0))) (int_add x0 x1).
Definition term120 (x0 : int) := real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term228 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term288 (a0 : Type') (a1 : Type') := forall y0 : finite_sum a0 a1, (@mk_finite_sum a0 a1 (@dest_finite_sum a0 a1 y0)) = y0.
Definition term61 (x0 : int) (x1 : int) := int_add (int_add x0 x1) (int_of_num (NUMERAL (BIT1 0))).
Definition term95 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term238 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term226 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_of_num (NUMERAL 0)).
Definition term65 (x0 : int) (x1 : int) := real_add (real_of_int (int_add x0 x1)) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term179 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term244 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term151 := S (Nat.add 0 0).
Definition term88 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term262 (x0 : nat) (x1 : nat) := forall y0 : nat, (@IN nat y0 (dotdot x0 x1)) = ((Peano.le x0 y0) /\ (Peano.le y0 x1)).
Definition term201 (x0 : int) (x1 : int) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_int x1)) (real_of_num (NUMERAL 0)).
Definition term86 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term112 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term266 (a0 : Type') (a1 : Type') := @IN nat (NUMERAL (BIT1 0)) (dotdot (NUMERAL (BIT1 0)) (Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1)))).
Definition term15 (x0 : nat) (x1 : nat) := int_le (int_of_num (NUMERAL (BIT1 0))) (int_add (int_of_num x0) (int_of_num x1)).
Definition term192 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)).
Definition term28 (x0 : int) (x1 : int) := ~ ((~ (int_le (int_of_num (NUMERAL (BIT1 0))) x0)) \/ (int_le (int_of_num (NUMERAL (BIT1 0))) (int_add x0 x1))).
Definition term170 (x0 : int) (x1 : int) := (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))).
Definition term188 (x0 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term71 (x0 : int) (x1 : int) := real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term227 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term221 (x0 : int) (x1 : int) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_int x1)).
Definition term159 := real_mul (real_of_num (NUMERAL 0)).
Definition term144 := real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term24 (x0 : int) := and (~ (~ (int_le (int_of_num (NUMERAL (BIT1 0))) x0))).
Definition term124 (x0 : int) (x1 : int) := real_ge (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term18 (x0 : nat) := int_le (int_of_num (NUMERAL 0)) (int_of_num x0).
Definition term93 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term282 (a0 : Type') (a1 : Type') (x0 : nat) := (fun y0 : nat => @IN nat y0 (dotdot (NUMERAL (BIT1 0)) (Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))) x0.
Definition term163 := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term111 := real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term230 (x0 : int) := ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term225 (x0 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_of_num (NUMERAL 0)).
Definition term194 (x0 : int) (x1 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))) (real_of_num (NUMERAL 0)).
Definition term184 (x0 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term31 (x0 : int) := and (int_le (int_of_num (NUMERAL 0)) x0).
Definition term25 (x0 : int) := and (int_le (int_of_num (NUMERAL (BIT1 0))) x0).
Definition term285 (a0 : Type') (a1 : Type') (x0 : nat) := @eq Prop ((fun y0 : nat => @IN nat y0 (dotdot (NUMERAL (BIT1 0)) (Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))) x0).
Definition term165 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)).
Definition term110 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term116 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term284 (a0 : Type') (a1 : Type') (x0 : nat) := @IN nat x0 (dotdot (NUMERAL (BIT1 0)) (Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1)))).
Definition term275 (a0 : Type') (a1 : Type') := exists y0 : nat, @IN nat y0 (dotdot (NUMERAL (BIT1 0)) (Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1)))).
Definition term11 (x0 : nat) (x1 : nat) := int_le (int_of_num (NUMERAL (BIT1 0))) (int_of_num (Nat.add x0 x1)).
Definition term80 (x0 : int) := real_sub (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term41 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term237 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term37 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ (~ ((int_le (int_of_num (NUMERAL 0)) x1) -> (~ (int_le (int_of_num (NUMERAL (BIT1 0))) x0)) \/ (int_le (int_of_num (NUMERAL (BIT1 0))) (int_add x0 x1)))).
Definition term265 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term166 (x0 : int) (x1 : int) := real_ge (real_sub (real_of_num (NUMERAL (BIT1 0))) (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term286 (a0 : Type') (a1 : Type') (x0 : nat) := @eq Prop (@IN nat x0 (dotdot (NUMERAL (BIT1 0)) (Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1))))).
Definition term263 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (@IN nat y0 (dotdot x0 x1)) = ((Peano.le x0 y0) /\ (Peano.le y0 x1))) x2.
Definition term100 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term200 (x0 : int) (x1 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x1) (real_of_num (NUMERAL 0)))) -> real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))) (real_of_int x1)) (real_of_num (NUMERAL 0)).
Definition term189 (x0 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term267 (a0 : Type') (a1 : Type') := (Peano.le (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))) /\ (Peano.le (NUMERAL (BIT1 0)) (Nat.add (@dimindex a0 (@UNIV a0)) (@dimindex a1 (@UNIV a1)))).
Definition term76 (x0 : int) (x1 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ ((real_le (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) /\ (real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))))).
Definition term81 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term75 (x0 : int) (x1 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ ((real_le (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) /\ (real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term257 (a0 : Type') (x0 : a0 -> Prop) := Peano.le (NUMERAL (BIT1 0)) (@dimindex a0 x0).
Definition term96 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term32 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) /\ (~ ((~ (int_le (int_of_num (NUMERAL (BIT1 0))) x0)) \/ (int_le (int_of_num (NUMERAL (BIT1 0))) (int_add x0 x1)))).
Definition term102 (x0 : real) := real_div x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term162 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term53 := real_of_num (NUMERAL (BIT1 0)).
Definition term180 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term222 (x0 : int) := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term253 (x0 : int) (x1 : int) := ~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ ((real_le (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) /\ (real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))))).
Definition term50 (x0 : int) := real_le (real_of_int (int_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term42 (x0 : int) := real_le (real_of_int (int_of_num (NUMERAL 0))) (real_of_int x0).
Definition term254 (x0 : nat) (x1 : nat) := (int_le (int_of_num (NUMERAL 0)) (int_of_num x0)) -> (int_le (int_of_num (NUMERAL 0)) (int_of_num x1)) -> (~ (int_le (int_of_num (NUMERAL (BIT1 0))) (int_of_num x0))) \/ (int_le (int_of_num (NUMERAL (BIT1 0))) (int_add (int_of_num x0) (int_of_num x1))).
Definition term236 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term74 (x0 : int) := and (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)).
Definition term72 (x0 : int) := and (real_le (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)).
Definition term33 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) /\ ((int_le (int_of_num (NUMERAL (BIT1 0))) x0) /\ (~ (int_le (int_of_num (NUMERAL (BIT1 0))) (int_add x0 x1)))).
Definition term138 := real_add (real_of_num (NUMERAL (BIT1 0))).
Definition term145 := real_add (real_of_num (NUMERAL (BIT1 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term20 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x1) -> (~ (int_le (int_of_num (NUMERAL (BIT1 0))) x0)) \/ (int_le (int_of_num (NUMERAL (BIT1 0))) (int_add x0 x1)).
Definition term136 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term243 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term178 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term233 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term191 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0).
Definition term187 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term4 (x0 : nat) (x1 : nat) := int_le (int_of_num x0) (int_of_num x1).
Definition term52 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term94 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term35 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term132 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term155 := real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term12 (x0 : nat) (x1 : nat) := int_of_num (Nat.add x0 x1).
Definition term220 (x0 : int) := real_mul (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term55 := real_le (real_of_num (NUMERAL (BIT1 0))).
Definition term142 (x0 : int) := real_add (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term133 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term176 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term208 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term269 := Peano.le (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term146 := real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term82 (x0 : nat) := real_div (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term47 := real_le (real_of_int (int_of_num (NUMERAL 0))).
Definition term239 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term89 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term66 (x0 : int) (x1 : int) := real_add (real_of_int (int_add x0 x1)).
Definition term101 := real_div (real_of_num (NUMERAL 0)).
Definition term235 := real_add (real_of_num (NUMERAL 0)).
Definition term251 (x0 : int) (x1 : int) := (~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ ((real_le (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) /\ (real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))))))) -> False.
Definition term69 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_add x0 x1) (int_of_num (NUMERAL (BIT1 0))))).
Definition term218 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term160 := real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term51 := int_of_num (NUMERAL (BIT1 0)).
Definition term234 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)).
Definition term13 (x0 : nat) (x1 : nat) := int_add (int_of_num x0) (int_of_num x1).
Definition term6 := NUMERAL (BIT1 0).
Definition term174 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term203 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_of_int x1)).
Definition term114 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term1 (x0 : nat) (x1 : nat) := (~ (Peano.le (NUMERAL (BIT1 0)) x0)) \/ (Peano.le (NUMERAL (BIT1 0)) (Nat.add x0 x1)).
Definition term185 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_of_int x0) (real_neg (real_of_num (NUMERAL (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term108 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term181 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term121 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term36 (x0 : int) (x1 : int) := (~ (int_le (int_of_num (NUMERAL (BIT1 0))) x0)) \/ (int_le (int_of_num (NUMERAL (BIT1 0))) (int_add x0 x1)).
Definition term79 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
