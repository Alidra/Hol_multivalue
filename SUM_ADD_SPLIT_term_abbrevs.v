Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term188 (x0 : nat) (x1 : nat) (x2 : nat) := @sum nat (dotdot x0 (Nat.add x1 x2)).
Definition term206 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat -> real) := (Peano.le x0 (Nat.add x1 (NUMERAL (BIT1 0)))) -> ((@sum nat (dotdot x0 (Nat.add x1 x2)) x3) = (real_add (@sum nat (dotdot x0 x1) x3) (@sum nat (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 x2)) x3))) = True.
Definition term120 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term136 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term185 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat -> real) (x4 : Prop) (x5 : Prop) := ((Peano.le x0 (Nat.add x1 (NUMERAL (BIT1 0)))) = x4) -> (x4 -> ((@sum nat (dotdot x0 (Nat.add x1 x2)) x3) = (real_add (@sum nat (dotdot x0 x1) x3) (@sum nat (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 x2)) x3))) = x5) -> ((Peano.le x0 (Nat.add x1 (NUMERAL (BIT1 0)))) -> (@sum nat (dotdot x0 (Nat.add x1 x2)) x3) = (real_add (@sum nat (dotdot x0 x1) x3) (@sum nat (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 x2)) x3))) = (x4 -> x5).
Definition term56 (x0 : nat) := real_div (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term0 (x0 : nat) (x1 : nat) := int_lt (int_of_num x0) (int_of_num x1).
Definition term68 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term97 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term104 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term80 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))).
Definition term111 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term112 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term172 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 (Nat.add x1 (NUMERAL (BIT1 0)))) -> (dotdot x0 (Nat.add x1 x2)) = (@UNION nat (dotdot x0 x1) (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 x2))).
Definition term55 (x0 : nat) := real_neg (real_of_num x0).
Definition term16 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ (~ (int_lt x0 (int_add x0 (int_of_num (NUMERAL (BIT1 0)))))).
Definition term23 := real_of_int (int_of_num (NUMERAL 0)).
Definition term48 (x0 : Prop) := ~ (~ x0).
Definition term24 := real_of_num (NUMERAL 0).
Definition term167 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le y0 (Nat.add y1 (NUMERAL (BIT1 0)))) -> (dotdot y0 (Nat.add y1 y2)) = (@UNION nat (dotdot y0 y1) (dotdot (Nat.add y1 (NUMERAL (BIT1 0))) (Nat.add y1 y2)))) x0.
Definition term149 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, (@DISJOINT nat (dotdot y0 y1) (dotdot y2 y3)) = ((Peano.lt y1 y2) \/ ((Peano.lt y3 y0) \/ ((Peano.lt y1 y0) \/ (Peano.lt y3 y2))))) x0.
Definition term30 (x0 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x0.
Definition term171 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Peano.le x0 (Nat.add x1 (NUMERAL (BIT1 0)))) -> (dotdot x0 (Nat.add x1 y0)) = (@UNION nat (dotdot x0 x1) (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 y0)))) x2.
Definition term95 (x0 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term189 (x0 : nat) (x1 : nat) (x2 : nat) := @sum nat (@UNION nat (dotdot x0 x1) (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 x2))).
Definition term21 := int_of_num (NUMERAL 0).
Definition term110 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term114 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term78 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term214 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term96 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term132 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term220 := fun y0 : nat -> real => forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.le y1 (Nat.add y2 (NUMERAL (BIT1 0)))) -> (@sum nat (dotdot y1 (Nat.add y2 y3)) y0) = (real_add (@sum nat (dotdot y1 y2) y0) (@sum nat (dotdot (Nat.add y2 (NUMERAL (BIT1 0))) (Nat.add y2 y3)) y0)).
Definition term63 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term85 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term2 (x0 : nat) := int_lt (int_of_num x0) (int_of_num (Nat.add x0 (NUMERAL (BIT1 0)))).
Definition term190 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat -> real) := @sum nat (@UNION nat (dotdot x0 x1) (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 x2))) x3.
Definition term99 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term35 (x0 : int) := real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0)))).
Definition term77 (x0 : int) := real_ge (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term158 (a0 : Type') (x0 : a0 -> real) := (fun y0 : a0 -> real => forall y1 : a0 -> Prop, forall y2 : a0 -> Prop, ((@FINITE a0 y1) /\ ((@FINITE a0 y2) /\ (@DISJOINT a0 y1 y2))) -> (@sum a0 (@UNION a0 y1 y2) y0) = (real_add (@sum a0 y1 y0) (@sum a0 y2 y0))) x0.
Definition term94 (x0 : int) := real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term200 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt (Nat.add x2 x1) x0) \/ ((Peano.lt x2 x0) \/ (Peano.lt (Nat.add x2 x1) (Nat.add x2 (NUMERAL (BIT1 0))))).
Definition term137 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_neg (real_of_num x1)).
Definition term14 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> int_lt x0 (int_add x0 (int_of_num (NUMERAL (BIT1 0)))).
Definition term108 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term103 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term82 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term54 := real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term142 (x0 : int) := ((~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))))) -> False) -> ~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term27 (x0 : int) := real_le (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term173 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.add x1 (NUMERAL (BIT1 0))).
Definition term222 := forall y0 : nat -> real, forall y1 : nat, forall y2 : nat, forall y3 : nat, (Peano.le y1 (Nat.add y2 (NUMERAL (BIT1 0)))) -> (@sum nat (dotdot y1 (Nat.add y2 y3)) y0) = (real_add (@sum nat (dotdot y1 y2) y0) (@sum nat (dotdot (Nat.add y2 (NUMERAL (BIT1 0))) (Nat.add y2 y3)) y0)).
Definition term76 (x0 : int) := real_ge (real_of_int x0).
Definition term9 (x0 : nat) := int_lt (int_of_num x0).
Definition term89 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term209 (x0 : nat) (x1 : nat) := (Peano.le x0 (Nat.add x1 (NUMERAL (BIT1 0)))) -> True.
Definition term58 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term181 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat -> real) := real_add (@sum nat (dotdot x0 x1) x3) (@sum nat (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 x2)) x3).
Definition term130 := real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term161 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) := forall y0 : a0 -> Prop, ((@FINITE a0 x0) /\ ((@FINITE a0 y0) /\ (@DISJOINT a0 x0 y0))) -> (@sum a0 (@UNION a0 x0 y0) x1) = (real_add (@sum a0 x0 x1) (@sum a0 y0 x1)).
Definition term92 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term75 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term106 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term36 (x0 : int) := real_add (real_of_int x0) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term70 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term146 (x0 : nat) := forall y0 : nat, @FINITE nat (dotdot x0 y0).
Definition term131 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term128 (x0 : int) := and (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term195 (x0 : nat) (x1 : nat) := @FINITE nat (dotdot (Nat.add x0 (NUMERAL (BIT1 0))) (Nat.add x0 x1)).
Definition term144 (x0 : nat) := (int_le (int_of_num (NUMERAL 0)) (int_of_num x0)) -> int_lt (int_of_num x0) (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))).
Definition term44 (x0 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term62 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term135 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term79 (x0 : int) := real_sub (real_of_int x0) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term109 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term102 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term74 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term154 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, (@DISJOINT nat (dotdot x1 x0) (dotdot x2 y0)) = ((Peano.lt x0 x2) \/ ((Peano.lt y0 x1) \/ ((Peano.lt x0 x1) \/ (Peano.lt y0 x2)))).
Definition term169 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le x0 (Nat.add y0 (NUMERAL (BIT1 0)))) -> (dotdot x0 (Nat.add y0 y1)) = (@UNION nat (dotdot x0 y0) (dotdot (Nat.add y0 (NUMERAL (BIT1 0))) (Nat.add y0 y1)))) x1.
Definition term160 (a0 : Type') (x0 : a0 -> real) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((@FINITE a0 y0) /\ ((@FINITE a0 y1) /\ (@DISJOINT a0 y0 y1))) -> (@sum a0 (@UNION a0 y0 y1) x0) = (real_add (@sum a0 y0 x0) (@sum a0 y1 x0))) x1.
Definition term147 (x0 : nat) (x1 : nat) := (fun y0 : nat => @FINITE nat (dotdot x0 y0)) x1.
Definition term26 := real_le (real_of_num (NUMERAL 0)).
Definition term33 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term138 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term175 (x0 : nat) (x1 : nat) (x2 : nat) := @UNION nat (dotdot x0 x1) (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 x2)).
Definition term40 (x0 : int) := real_add (real_of_int x0).
Definition term11 (x0 : nat) := (fun y0 : nat => int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) x0.
Definition term176 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term191 (x0 : nat -> Prop) (x1 : nat -> Prop) (x2 : nat -> real) := ((@FINITE nat x0) /\ ((@FINITE nat x1) /\ (@DISJOINT nat x0 x1))) -> (@sum nat (@UNION nat x0 x1) x2) = (real_add (@sum nat x0 x2) (@sum nat x1 x2)).
Definition term163 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := ((@FINITE a0 x0) /\ ((@FINITE a0 x1) /\ (@DISJOINT a0 x0 x1))) -> (@sum a0 (@UNION a0 x0 x1) x2) = (real_add (@sum a0 x0 x2) (@sum a0 x1 x2)).
Definition term140 := and ((NUMERAL 0) = (NUMERAL 0)).
Definition term98 (x0 : int) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term22 (x0 : nat) := real_of_int (int_of_num x0).
Definition term197 (x0 : nat) (x1 : nat) (x2 : nat) := @DISJOINT nat (dotdot x0 x1) (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 x2)).
Definition term155 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => (@DISJOINT nat (dotdot x1 x0) (dotdot x2 y0)) = ((Peano.lt x0 x2) \/ ((Peano.lt y0 x1) \/ ((Peano.lt x0 x1) \/ (Peano.lt y0 x2))))) x3.
Definition term117 := real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term129 (x0 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term113 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term69 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term34 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term100 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term61 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term139 := ((NUMERAL 0) = (NUMERAL 0)) /\ ((NUMERAL (BIT1 0)) = (NUMERAL 0)).
Definition term90 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term210 (x0 : nat) (x1 : nat) (x2 : nat -> real) := fun y0 : nat => (Peano.le x0 (Nat.add x1 (NUMERAL (BIT1 0)))) -> (@sum nat (dotdot x0 (Nat.add x1 y0)) x2) = (real_add (@sum nat (dotdot x0 x1) x2) (@sum nat (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 y0)) x2)).
Definition term105 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term201 (x0 : nat) (x1 : nat) (x2 : nat) := True \/ ((Peano.lt (Nat.add x2 x1) x0) \/ ((Peano.lt x2 x0) \/ (Peano.lt (Nat.add x2 x1) (Nat.add x2 (NUMERAL (BIT1 0)))))).
Definition term223 := forall y0 : nat -> real, True.
Definition term207 (x0 : nat) (x1 : nat -> real) (x2 : nat) (x3 : nat) := ((Peano.le x2 (Nat.add x3 (NUMERAL (BIT1 0)))) -> ((@sum nat (dotdot x2 (Nat.add x3 x0)) x1) = (real_add (@sum nat (dotdot x2 x3) x1) (@sum nat (dotdot (Nat.add x3 (NUMERAL (BIT1 0))) (Nat.add x3 x0)) x1))) = True) -> ((Peano.le x2 (Nat.add x3 (NUMERAL (BIT1 0)))) -> (@sum nat (dotdot x2 (Nat.add x3 x0)) x1) = (real_add (@sum nat (dotdot x2 x3) x1) (@sum nat (dotdot (Nat.add x3 (NUMERAL (BIT1 0))) (Nat.add x3 x0)) x1))) = ((Peano.le x2 (Nat.add x3 (NUMERAL (BIT1 0)))) -> True).
Definition term157 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x3) \/ ((Peano.lt x2 x1) \/ ((Peano.lt x0 x1) \/ (Peano.lt x2 x3))).
Definition term219 (x0 : nat -> real) := forall y0 : nat, forall y1 : nat, forall y2 : nat, (Peano.le y0 (Nat.add y1 (NUMERAL (BIT1 0)))) -> (@sum nat (dotdot y0 (Nat.add y1 y2)) x0) = (real_add (@sum nat (dotdot y0 y1) x0) (@sum nat (dotdot (Nat.add y1 (NUMERAL (BIT1 0))) (Nat.add y1 y2)) x0)).
Definition term217 (x0 : nat) (x1 : nat -> real) := forall y0 : nat, forall y1 : nat, (Peano.le x0 (Nat.add y0 (NUMERAL (BIT1 0)))) -> (@sum nat (dotdot x0 (Nat.add y0 y1)) x1) = (real_add (@sum nat (dotdot x0 y0) x1) (@sum nat (dotdot (Nat.add y0 (NUMERAL (BIT1 0))) (Nat.add y0 y1)) x1)).
Definition term168 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Peano.le x0 (Nat.add y0 (NUMERAL (BIT1 0)))) -> (dotdot x0 (Nat.add y0 y1)) = (@UNION nat (dotdot x0 y0) (dotdot (Nat.add y0 (NUMERAL (BIT1 0))) (Nat.add y0 y1))).
Definition term152 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, (@DISJOINT nat (dotdot x1 x0) (dotdot y0 y1)) = ((Peano.lt x0 y0) \/ ((Peano.lt y1 x1) \/ ((Peano.lt x0 x1) \/ (Peano.lt y1 y0)))).
Definition term150 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, (@DISJOINT nat (dotdot x0 y0) (dotdot y1 y2)) = ((Peano.lt y0 y1) \/ ((Peano.lt y2 x0) \/ ((Peano.lt y0 x0) \/ (Peano.lt y2 y1)))).
Definition term122 (x0 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term43 (x0 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term87 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term153 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, (@DISJOINT nat (dotdot x1 x0) (dotdot y0 y1)) = ((Peano.lt x0 y0) \/ ((Peano.lt y1 x1) \/ ((Peano.lt x0 x1) \/ (Peano.lt y1 y0))))) x2.
Definition term151 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (@DISJOINT nat (dotdot x0 y0) (dotdot y1 y2)) = ((Peano.lt y0 y1) \/ ((Peano.lt y2 x0) \/ ((Peano.lt y0 x0) \/ (Peano.lt y2 y1))))) x1.
Definition term13 (x0 : int) := ~ (~ ((int_le (int_of_num (NUMERAL 0)) x0) -> int_lt x0 (int_add x0 (int_of_num (NUMERAL (BIT1 0)))))).
Definition term186 (x0 : nat) (x1 : nat -> real) (x2 : nat) (x3 : nat) (x4 : Prop) := ((Peano.le x2 (Nat.add x3 (NUMERAL (BIT1 0)))) = (Peano.le x2 (Nat.add x3 (NUMERAL (BIT1 0))))) -> ((Peano.le x2 (Nat.add x3 (NUMERAL (BIT1 0)))) -> ((@sum nat (dotdot x2 (Nat.add x3 x0)) x1) = (real_add (@sum nat (dotdot x2 x3) x1) (@sum nat (dotdot (Nat.add x3 (NUMERAL (BIT1 0))) (Nat.add x3 x0)) x1))) = x4) -> ((Peano.le x2 (Nat.add x3 (NUMERAL (BIT1 0)))) -> (@sum nat (dotdot x2 (Nat.add x3 x0)) x1) = (real_add (@sum nat (dotdot x2 x3) x1) (@sum nat (dotdot (Nat.add x3 (NUMERAL (BIT1 0))) (Nat.add x3 x0)) x1))) = ((Peano.le x2 (Nat.add x3 (NUMERAL (BIT1 0)))) -> x4).
Definition term213 := forall y0 : nat, True.
Definition term199 (x0 : nat) := or (Peano.lt x0 (Nat.add x0 (NUMERAL (BIT1 0)))).
Definition term91 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term66 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term126 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term3 (x0 : nat) := Nat.add x0 (NUMERAL (BIT1 0)).
Definition term125 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))).
Definition term204 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat -> real) := @eq real (@sum nat (dotdot x0 (Nat.add x1 x2)) x3).
Definition term134 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term203 (x0 : nat) (x1 : nat) (x2 : nat) := (@FINITE nat (dotdot x0 x1)) /\ ((@FINITE nat (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 x2))) /\ (@DISJOINT nat (dotdot x0 x1) (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 x2)))).
Definition term31 (x0 : int) := int_add x0 (int_of_num (NUMERAL (BIT1 0))).
Definition term174 (x0 : nat) (x1 : nat) (x2 : nat) := dotdot x0 (Nat.add x1 x2).
Definition term107 := S (Nat.add 0 0).
Definition term59 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term211 := fun y0 : nat => True.
Definition term57 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term84 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term156 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @DISJOINT nat (dotdot x0 x1) (dotdot x2 x3).
Definition term187 (x0 : nat) (x1 : nat -> real) (x2 : nat) (x3 : nat) (x4 : Prop) := ((Peano.le x2 (Nat.add x3 (NUMERAL (BIT1 0)))) -> ((@sum nat (dotdot x2 (Nat.add x3 x0)) x1) = (real_add (@sum nat (dotdot x2 x3) x1) (@sum nat (dotdot (Nat.add x3 (NUMERAL (BIT1 0))) (Nat.add x3 x0)) x1))) = x4) -> ((Peano.le x2 (Nat.add x3 (NUMERAL (BIT1 0)))) -> (@sum nat (dotdot x2 (Nat.add x3 x0)) x1) = (real_add (@sum nat (dotdot x2 x3) x1) (@sum nat (dotdot (Nat.add x3 (NUMERAL (BIT1 0))) (Nat.add x3 x0)) x1))) = ((Peano.le x2 (Nat.add x3 (NUMERAL (BIT1 0)))) -> x4).
Definition term183 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat -> real) (x4 : Prop) := forall y0 : Prop, ((Peano.le x0 (Nat.add x1 (NUMERAL (BIT1 0)))) = x4) -> (x4 -> ((@sum nat (dotdot x0 (Nat.add x1 x2)) x3) = (real_add (@sum nat (dotdot x0 x1) x3) (@sum nat (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 x2)) x3))) = y0) -> ((Peano.le x0 (Nat.add x1 (NUMERAL (BIT1 0)))) -> (@sum nat (dotdot x0 (Nat.add x1 x2)) x3) = (real_add (@sum nat (dotdot x0 x1) x3) (@sum nat (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 x2)) x3))) = (x4 -> y0).
Definition term177 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term7 (x0 : nat) := int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0))).
Definition term164 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (@FINITE a0 x0) /\ ((@FINITE a0 x1) /\ (@DISJOINT a0 x0 x1)).
Definition term196 (x0 : nat) (x1 : nat) := and (@FINITE nat (dotdot (Nat.add x0 (NUMERAL (BIT1 0))) (Nat.add x0 x1))).
Definition term18 (x0 : int) := int_lt x0 (int_add x0 (int_of_num (NUMERAL (BIT1 0)))).
Definition term115 := real_mul (real_of_num (NUMERAL 0)).
Definition term179 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat -> real) := forall y0 : Prop, forall y1 : Prop, ((Peano.le x0 (Nat.add x1 (NUMERAL (BIT1 0)))) = y0) -> (y0 -> ((@sum nat (dotdot x0 (Nat.add x1 x2)) x3) = (real_add (@sum nat (dotdot x0 x1) x3) (@sum nat (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 x2)) x3))) = y1) -> ((Peano.le x0 (Nat.add x1 (NUMERAL (BIT1 0)))) -> (@sum nat (dotdot x0 (Nat.add x1 x2)) x3) = (real_add (@sum nat (dotdot x0 x1) x3) (@sum nat (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 x2)) x3))) = (y0 -> y1).
Definition term178 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term42 (x0 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))).
Definition term159 (a0 : Type') (x0 : a0 -> real) := forall y0 : a0 -> Prop, forall y1 : a0 -> Prop, ((@FINITE a0 y0) /\ ((@FINITE a0 y1) /\ (@DISJOINT a0 y0 y1))) -> (@sum a0 (@UNION a0 y0 y1) x0) = (real_add (@sum a0 y0 x0) (@sum a0 y1 x0)).
Definition term29 (x0 : int) := ~ (int_lt x0 (int_add x0 (int_of_num (NUMERAL (BIT1 0))))).
Definition term193 (x0 : nat) (x1 : nat) := dotdot (Nat.add x0 (NUMERAL (BIT1 0))) (Nat.add x0 x1).
Definition term12 (x0 : nat) := int_le (int_of_num (NUMERAL 0)) (int_of_num x0).
Definition term64 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term202 (x0 : nat) (x1 : nat) (x2 : nat) := (@FINITE nat (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 x2))) /\ (@DISJOINT nat (dotdot x0 x1) (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 x2))).
Definition term119 := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term148 (x0 : nat) (x1 : nat) := @FINITE nat (dotdot x0 x1).
Definition term83 := real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term15 (x0 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) x0) -> int_lt x0 (int_add x0 (int_of_num (NUMERAL (BIT1 0))))).
Definition term184 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat -> real) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => ((Peano.le x0 (Nat.add x1 (NUMERAL (BIT1 0)))) = x4) -> (x4 -> ((@sum nat (dotdot x0 (Nat.add x1 x2)) x3) = (real_add (@sum nat (dotdot x0 x1) x3) (@sum nat (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 x2)) x3))) = y0) -> ((Peano.le x0 (Nat.add x1 (NUMERAL (BIT1 0)))) -> (@sum nat (dotdot x0 (Nat.add x1 x2)) x3) = (real_add (@sum nat (dotdot x0 x1) x3) (@sum nat (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 x2)) x3))) = (x4 -> y0)) x5.
Definition term194 (x0 : nat) (x1 : nat) := and (@FINITE nat (dotdot x0 x1)).
Definition term45 (x0 : int) := and (int_le (int_of_num (NUMERAL 0)) x0).
Definition term47 (x0 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term88 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term221 := fun y0 : nat -> real => True.
Definition term51 (x0 : int) := real_sub (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term19 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term162 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> real) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((@FINITE a0 x0) /\ ((@FINITE a0 y0) /\ (@DISJOINT a0 x0 y0))) -> (@sum a0 (@UNION a0 x0 y0) x1) = (real_add (@sum a0 x0 x1) (@sum a0 y0 x1))) x2.
Definition term49 (x0 : int) := ~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)))).
Definition term71 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term52 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term224 (x0 : Prop) := forall y0 : nat -> real, x0.
Definition term67 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term73 (x0 : real) := real_div x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term118 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term39 := real_of_num (NUMERAL (BIT1 0)).
Definition term20 (x0 : int) := real_le (real_of_int (int_of_num (NUMERAL 0))) (real_of_int x0).
Definition term124 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term180 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat -> real) := @sum nat (dotdot x0 (Nat.add x1 x2)) x3.
Definition term46 (x0 : int) := and (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)).
Definition term192 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat -> real) := ((@FINITE nat (dotdot x0 x1)) /\ ((@FINITE nat (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 x2))) /\ (@DISJOINT nat (dotdot x0 x1) (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 x2))))) -> (@sum nat (@UNION nat (dotdot x0 x1) (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 x2))) x3) = (real_add (@sum nat (dotdot x0 x1) x3) (@sum nat (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 x2)) x3)).
Definition term198 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.lt x2 (Nat.add x2 (NUMERAL (BIT1 0)))) \/ ((Peano.lt (Nat.add x2 x1) x0) \/ ((Peano.lt x2 x0) \/ (Peano.lt (Nat.add x2 x1) (Nat.add x2 (NUMERAL (BIT1 0)))))).
Definition term93 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term145 (x0 : nat) := (fun y0 : nat => forall y1 : nat, @FINITE nat (dotdot y0 y1)) x0.
Definition term133 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term215 (x0 : Prop) := forall y0 : nat, x0.
Definition term38 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term65 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term212 (x0 : nat) (x1 : nat) (x2 : nat -> real) := forall y0 : nat, (Peano.le x0 (Nat.add x1 (NUMERAL (BIT1 0)))) -> (@sum nat (dotdot x0 (Nat.add x1 y0)) x2) = (real_add (@sum nat (dotdot x0 x1) x2) (@sum nat (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 y0)) x2)).
Definition term170 (x0 : nat) (x1 : nat) := forall y0 : nat, (Peano.le x0 (Nat.add x1 (NUMERAL (BIT1 0)))) -> (dotdot x0 (Nat.add x1 y0)) = (@UNION nat (dotdot x0 x1) (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 y0))).
Definition term208 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat -> real) := (Peano.le x0 (Nat.add x1 (NUMERAL (BIT1 0)))) -> (@sum nat (dotdot x0 (Nat.add x1 x2)) x3) = (real_add (@sum nat (dotdot x0 x1) x3) (@sum nat (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 x2)) x3)).
Definition term6 (x0 : nat) := int_of_num (Nat.add x0 (NUMERAL (BIT1 0))).
Definition term17 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term41 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term4 (x0 : nat) (x1 : nat) := int_of_num (Nat.add x0 x1).
Definition term121 (x0 : int) := real_mul (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term165 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := @sum a0 (@UNION a0 x0 x1) x2.
Definition term81 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term101 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term53 (x0 : nat) := real_div (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term25 := real_le (real_of_int (int_of_num (NUMERAL 0))).
Definition term127 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term166 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) (x2 : a0 -> real) := real_add (@sum a0 x0 x2) (@sum a0 x1 x2).
Definition term182 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat -> real) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((Peano.le x0 (Nat.add x1 (NUMERAL (BIT1 0)))) = y0) -> (y0 -> ((@sum nat (dotdot x0 (Nat.add x1 x2)) x3) = (real_add (@sum nat (dotdot x0 x1) x3) (@sum nat (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 x2)) x3))) = y1) -> ((Peano.le x0 (Nat.add x1 (NUMERAL (BIT1 0)))) -> (@sum nat (dotdot x0 (Nat.add x1 x2)) x3) = (real_add (@sum nat (dotdot x0 x1) x3) (@sum nat (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 x2)) x3))) = (y0 -> y1)) x4.
Definition term60 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term72 := real_div (real_of_num (NUMERAL 0)).
Definition term28 (x0 : int) (x1 : int) := ~ (int_lt x0 x1).
Definition term123 := real_add (real_of_num (NUMERAL 0)).
Definition term141 (x0 : int) := (~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))))) -> False.
Definition term116 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term37 := int_of_num (NUMERAL (BIT1 0)).
Definition term1 (x0 : nat) := Peano.lt x0 (Nat.add x0 (NUMERAL (BIT1 0))).
Definition term32 (x0 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x0).
Definition term5 (x0 : nat) (x1 : nat) := int_add (int_of_num x0) (int_of_num x1).
Definition term216 (x0 : nat) (x1 : nat -> real) := fun y0 : nat => forall y1 : nat, (Peano.le x0 (Nat.add y0 (NUMERAL (BIT1 0)))) -> (@sum nat (dotdot x0 (Nat.add y0 y1)) x1) = (real_add (@sum nat (dotdot x0 y0) x1) (@sum nat (dotdot (Nat.add y0 (NUMERAL (BIT1 0))) (Nat.add y0 y1)) x1)).
Definition term8 := NUMERAL (BIT1 0).
Definition term218 (x0 : nat -> real) := fun y0 : nat => forall y1 : nat, forall y2 : nat, (Peano.le y0 (Nat.add y1 (NUMERAL (BIT1 0)))) -> (@sum nat (dotdot y0 (Nat.add y1 y2)) x0) = (real_add (@sum nat (dotdot y0 y1) x0) (@sum nat (dotdot (Nat.add y1 (NUMERAL (BIT1 0))) (Nat.add y1 y2)) x0)).
Definition term143 (x0 : int) := ~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term86 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term10 (x0 : nat) := int_lt (int_of_num x0) (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))).
Definition term205 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat -> real) := @eq real (real_add (@sum nat (dotdot x0 x1) x3) (@sum nat (dotdot (Nat.add x1 (NUMERAL (BIT1 0))) (Nat.add x1 x2)) x3)).
Definition term50 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
