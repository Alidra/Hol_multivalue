Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term355 (a0 : Type') (x0 : a0) := ~ (@IN a0 x0 (@EMPTY a0)).
Definition term408 (x0 : nat) (x1 : nat) (x2 : nat) := @IN nat x0 (dotdot x1 x2).
Definition term314 (x0 : nat) (x1 : nat) := (fun y0 : nat => (@CARD nat (dotdot x0 (Nat.add x0 y0))) = (Nat.add y0 (NUMERAL (BIT1 0)))) (S x1).
Definition term448 (x0 : nat) (x1 : nat) (x2 : Prop) (x3 : nat) (x4 : nat) := (fun y0 : nat => ((@IN nat (S (Nat.add x0 x1)) (dotdot x0 (Nat.add x0 x1))) = x2) -> (x2 -> (@CARD nat (dotdot x0 (Nat.add x0 x1))) = x3) -> ((~ x2) -> (S (@CARD nat (dotdot x0 (Nat.add x0 x1)))) = y0) -> (@COND nat (@IN nat (S (Nat.add x0 x1)) (dotdot x0 (Nat.add x0 x1))) (@CARD nat (dotdot x0 (Nat.add x0 x1))) (S (@CARD nat (dotdot x0 (Nat.add x0 x1))))) = (@COND nat x2 x3 y0)) x4.
Definition term456 (x0 : nat) (x1 : nat) (x2 : nat) := (False -> (@CARD nat (dotdot x0 (Nat.add x0 x1))) = (Nat.add x1 (NUMERAL (BIT1 0)))) -> ((~ False) -> (S (@CARD nat (dotdot x0 (Nat.add x0 x1)))) = x2) -> (@COND nat (@IN nat (S (Nat.add x0 x1)) (dotdot x0 (Nat.add x0 x1))) (@CARD nat (dotdot x0 (Nat.add x0 x1))) (S (@CARD nat (dotdot x0 (Nat.add x0 x1))))) = (@COND nat False (Nat.add x1 (NUMERAL (BIT1 0))) x2).
Definition term127 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term21 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> ~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x0).
Definition term143 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term261 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term63 (x0 : nat) := real_div (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term75 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term104 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term111 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term87 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))).
Definition term118 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term188 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term397 := (~ False) -> (S (@CARD nat (@EMPTY nat))) = (NUMERAL (BIT1 0)).
Definition term327 (x0 : nat) := fun y0 : nat => (fun y1 : nat => (@CARD nat (dotdot x0 (Nat.add x0 y1))) = (Nat.add y1 (NUMERAL (BIT1 0)))) y0.
Definition term210 := real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term119 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term256 (x0 : int) (x1 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term62 (x0 : nat) := real_neg (real_of_num x0).
Definition term16 (x0 : nat) := int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x0).
Definition term447 (x0 : nat) (x1 : nat) (x2 : Prop) (x3 : nat) := forall y0 : nat, ((@IN nat (S (Nat.add x0 x1)) (dotdot x0 (Nat.add x0 x1))) = x2) -> (x2 -> (@CARD nat (dotdot x0 (Nat.add x0 x1))) = x3) -> ((~ x2) -> (S (@CARD nat (dotdot x0 (Nat.add x0 x1)))) = y0) -> (@COND nat (@IN nat (S (Nat.add x0 x1)) (dotdot x0 (Nat.add x0 x1))) (@CARD nat (dotdot x0 (Nat.add x0 x1))) (S (@CARD nat (dotdot x0 (Nat.add x0 x1))))) = (@COND nat x2 x3 y0).
Definition term387 (x0 : nat) (x1 : Prop) (x2 : nat) := forall y0 : nat, ((@IN nat x0 (@EMPTY nat)) = x1) -> (x1 -> (@CARD nat (@EMPTY nat)) = x2) -> ((~ x1) -> (S (@CARD nat (@EMPTY nat))) = y0) -> (@COND nat (@IN nat x0 (@EMPTY nat)) (@CARD nat (@EMPTY nat)) (S (@CARD nat (@EMPTY nat)))) = (@COND nat x1 x2 y0).
Definition term450 (x0 : nat) (x1 : nat) := (Peano.le x0 (S (Nat.add x0 x1))) /\ (Peano.le (S (Nat.add x0 x1)) (Nat.add x0 x1)).
Definition term34 := real_of_int (int_of_num (NUMERAL 0)).
Definition term55 (x0 : Prop) := ~ (~ x0).
Definition term35 := real_of_num (NUMERAL 0).
Definition term403 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (@IN nat y2 (dotdot y0 y1)) = ((Peano.le y0 y2) /\ (Peano.le y2 y1))) x0.
Definition term23 (x0 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x0.
Definition term179 (x0 : int) (x1 : int) := int_add x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))).
Definition term224 := real_div (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term102 (x0 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term454 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (False -> (@CARD nat (dotdot x0 (Nat.add x0 x1))) = x2) -> ((~ False) -> (S (@CARD nat (dotdot x0 (Nat.add x0 x1)))) = x3) -> (@COND nat (@IN nat (S (Nat.add x0 x1)) (dotdot x0 (Nat.add x0 x1))) (@CARD nat (dotdot x0 (Nat.add x0 x1))) (S (@CARD nat (dotdot x0 (Nat.add x0 x1))))) = (@COND nat False x2 x3).
Definition term226 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term186 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))).
Definition term390 (x0 : nat) (x1 : nat) (x2 : nat) := ((@IN nat x0 (@EMPTY nat)) = False) -> (False -> (@CARD nat (@EMPTY nat)) = x1) -> ((~ False) -> (S (@CARD nat (@EMPTY nat))) = x2) -> (@COND nat (@IN nat x0 (@EMPTY nat)) (@CARD nat (@EMPTY nat)) (S (@CARD nat (@EMPTY nat)))) = (@COND nat False x1 x2).
Definition term158 (x0 : nat) (x1 : nat) := Peano.le x1 (Nat.add x0 (Nat.add x1 (NUMERAL (BIT1 0)))).
Definition term332 := ((0 = 0) = True) /\ ((forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))))).
Definition term331 := (forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1)) /\ (((0 = 0) = True) /\ ((forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))))))).
Definition term444 (x0 : nat) (x1 : nat) (x2 : Prop) := (fun y0 : Prop => forall y1 : nat, forall y2 : nat, ((@IN nat (S (Nat.add x0 x1)) (dotdot x0 (Nat.add x0 x1))) = y0) -> (y0 -> (@CARD nat (dotdot x0 (Nat.add x0 x1))) = y1) -> ((~ y0) -> (S (@CARD nat (dotdot x0 (Nat.add x0 x1)))) = y2) -> (@COND nat (@IN nat (S (Nat.add x0 x1)) (dotdot x0 (Nat.add x0 x1))) (@CARD nat (dotdot x0 (Nat.add x0 x1))) (S (@CARD nat (dotdot x0 (Nat.add x0 x1))))) = (@COND nat y0 y1 y2)) x2.
Definition term335 := (forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))).
Definition term333 := (forall y0 : nat, ((BIT0 y0) = 0) = (y0 = 0)) /\ ((forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))))))).
Definition term6 (x0 : nat) := ~ (Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x0).
Definition term32 := int_of_num (NUMERAL 0).
Definition term15 (x0 : nat) := int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))).
Definition term298 (x0 : int) (x1 : int) := ((~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (real_le (real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))))) -> False) -> ~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (real_le (real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))).
Definition term394 (x0 : nat) (x1 : nat) := ((~ False) -> (S (@CARD nat (@EMPTY nat))) = x1) -> (@COND nat (@IN nat x0 (@EMPTY nat)) (@CARD nat (@EMPTY nat)) (S (@CARD nat (@EMPTY nat)))) = (@COND nat False (NUMERAL 0) x1).
Definition term208 := ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term117 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term216 := real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term121 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term196 (x0 : int) (x1 : int) := real_ge (real_sub (real_of_int x1) (real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term85 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term155 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.add (Nat.add x0 x1) (NUMERAL (BIT1 0))).
Definition term103 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term289 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term139 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term402 (x0 : nat) := (~ (Peano.le (S x0) x0)) -> (Peano.le (S x0) x0) = False.
Definition term178 (x0 : int) (x1 : int) := int_le (int_add (int_add x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0))))) (int_of_num (NUMERAL (BIT1 0)))) x1.
Definition term353 (x0 : nat) := NUMERAL (S x0).
Definition term253 (x0 : int) (x1 : int) := real_ge (real_sub (real_of_int x1) (real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term184 (x0 : int) (x1 : int) := real_of_int (int_add x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0))))).
Definition term362 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @CARD a0 (@INSERT a0 x0 x1).
Definition term280 (x0 : int) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term166 (x0 : int) (x1 : int) := ~ (~ ((int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x1) -> int_le x1 (int_add x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0))))))).
Definition term395 := S (NUMERAL 0).
Definition term70 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term236 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term92 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term296 := S (Nat.add (BIT1 0) 0).
Definition term421 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term339 := (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)).
Definition term416 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 (S y0)) -> (dotdot x0 (S y0)) = (@INSERT nat (S y0) (dotdot x0 y0))) x1.
Definition term173 (x0 : int) (x1 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x1) -> int_le x1 (int_add x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))).
Definition term364 (x0 : nat) := (fun y0 : nat => (dotdot y0 y0) = (@INSERT nat y0 (@EMPTY nat))) x0.
Definition term452 (x0 : nat) (x1 : nat) := Peano.le (S (Nat.add x0 x1)) (Nat.add x0 x1).
Definition term172 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ ((int_le (int_of_num (NUMERAL 0)) x1) /\ (~ (int_le x1 (int_add x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))))).
Definition term106 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term43 (x0 : int) := real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0)))).
Definition term84 (x0 : int) := real_ge (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term191 (x0 : int) (x1 : int) := real_le (real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term346 (x0 : nat) := forall y0 : nat, ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0).
Definition term342 (x0 : nat) := forall y0 : nat, ((BIT1 x0) = (BIT1 y0)) = (x0 = y0).
Definition term360 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@CARD a0 (@INSERT a0 x0 y0)) = (@COND nat (@IN a0 x0 y0) (@CARD a0 y0) (S (@CARD a0 y0)))) x1.
Definition term328 (x0 : nat) := forall y0 : nat, (fun y1 : nat => (@CARD nat (dotdot x0 (Nat.add x0 y1))) = (Nat.add y1 (NUMERAL (BIT1 0)))) y0.
Definition term250 (x0 : int) := real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))))).
Definition term101 (x0 : int) := real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term202 := real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term378 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) := forall y0 : a0, (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = y0) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 y0).
Definition term144 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_neg (real_of_num x1)).
Definition term206 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term204 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term115 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term110 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term234 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term89 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term323 (x0 : nat) := ((fun y0 : nat => (@CARD nat (dotdot x0 (Nat.add x0 y0))) = (Nat.add y0 (NUMERAL (BIT1 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (@CARD nat (dotdot x0 (Nat.add x0 y1))) = (Nat.add y1 (NUMERAL (BIT1 0)))) y0) -> (fun y1 : nat => (@CARD nat (dotdot x0 (Nat.add x0 y1))) = (Nat.add y1 (NUMERAL (BIT1 0)))) (S y0)).
Definition term460 (x0 : nat) (x1 : nat) := ((~ False) -> (S (@CARD nat (dotdot x0 (Nat.add x0 x1)))) = (S (Nat.add x1 (NUMERAL (BIT1 0))))) -> (@COND nat (@IN nat (S (Nat.add x0 x1)) (dotdot x0 (Nat.add x0 x1))) (@CARD nat (dotdot x0 (Nat.add x0 x1))) (S (@CARD nat (dotdot x0 (Nat.add x0 x1))))) = (@COND nat False (Nat.add x1 (NUMERAL (BIT1 0))) (S (Nat.add x1 (NUMERAL (BIT1 0))))).
Definition term420 (x0 : nat) (x1 : nat) := @INSERT nat (S x1) (dotdot x0 x1).
Definition term61 := real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term170 (x0 : int) (x1 : int) := int_le x1 (int_add x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0))))).
Definition term374 (x0 : nat) (x1 : nat -> Prop) := (@FINITE nat x1) -> (@CARD nat (@INSERT nat x0 x1)) = (@COND nat (@IN nat x0 x1) (@CARD nat x1) (S (@CARD nat x1))).
Definition term361 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> (@CARD a0 (@INSERT a0 x0 x1)) = (@COND nat (@IN a0 x0 x1) (@CARD a0 x1) (S (@CARD a0 x1))).
Definition term20 (x0 : int) := ~ (~ ((int_le (int_of_num (NUMERAL 0)) x0) -> ~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x0))).
Definition term149 (x0 : int) := ((~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))))) -> False) -> ~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term38 (x0 : int) := real_le (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term272 (x0 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0))).
Definition term306 (x0 : nat) := @CARD nat (dotdot x0 (Nat.add x0 (NUMERAL 0))).
Definition term367 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term83 (x0 : int) := real_ge (real_of_int x0).
Definition term190 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_add x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0))))) (int_of_num (NUMERAL (BIT1 0))))).
Definition term313 (x0 : nat) (x1 : nat) := imp ((@CARD nat (dotdot x0 (Nat.add x0 x1))) = (Nat.add x1 (NUMERAL (BIT1 0)))).
Definition term187 (x0 : int) (x1 : int) := real_add (real_of_int (int_add x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))).
Definition term192 (x0 : int) (x1 : int) := real_le (real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1).
Definition term317 (x0 : nat) (x1 : nat) := ((fun y0 : nat => (@CARD nat (dotdot x0 (Nat.add x0 y0))) = (Nat.add y0 (NUMERAL (BIT1 0)))) x1) -> (fun y0 : nat => (@CARD nat (dotdot x0 (Nat.add x0 y0))) = (Nat.add y0 (NUMERAL (BIT1 0)))) (S x1).
Definition term383 := S (@CARD nat (@EMPTY nat)).
Definition term181 (x0 : int) (x1 : int) := int_add (int_add x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0))))) (int_of_num (NUMERAL (BIT1 0))).
Definition term294 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL (BIT1 0)))).
Definition term96 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term175 (x0 : int) (x1 : int) := ~ (int_le x0 x1).
Definition term349 := ((S 0) = (BIT1 0)) /\ ((forall y0 : nat, (S (BIT0 y0)) = (BIT1 y0)) /\ (forall y0 : nat, (S (BIT1 y0)) = (BIT0 (S y0)))).
Definition term303 (x0 : nat) := (((fun y0 : nat => (@CARD nat (dotdot x0 (Nat.add x0 y0))) = (Nat.add y0 (NUMERAL (BIT1 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (@CARD nat (dotdot x0 (Nat.add x0 y1))) = (Nat.add y1 (NUMERAL (BIT1 0)))) y0) -> (fun y1 : nat => (@CARD nat (dotdot x0 (Nat.add x0 y1))) = (Nat.add y1 (NUMERAL (BIT1 0)))) (S y0))) -> forall y0 : nat, (fun y1 : nat => (@CARD nat (dotdot x0 (Nat.add x0 y1))) = (Nat.add y1 (NUMERAL (BIT1 0)))) y0.
Definition term25 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ (~ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x0))).
Definition term245 := real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term65 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term372 (x0 : nat) := dotdot x0 (Nat.add x0 (NUMERAL 0)).
Definition term436 (x0 : nat) (x1 : nat) := @CARD nat (@INSERT nat (S (Nat.add x0 x1)) (dotdot x0 (Nat.add x0 x1))).
Definition term183 (x0 : int) (x1 : int) := real_add (real_of_int (int_add x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term458 (x0 : nat) := S (Nat.add x0 (NUMERAL (BIT1 0))).
Definition term288 := real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term137 := real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term435 (x0 : nat) (x1 : nat) := @INSERT nat (S (Nat.add x0 x1)) (dotdot x0 (Nat.add x0 x1)).
Definition term180 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_add x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0))))) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x1).
Definition term358 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@CARD a0 (@INSERT a0 y0 y1)) = (@COND nat (@IN a0 y0 y1) (@CARD a0 y1) (S (@CARD a0 y1)))) x0.
Definition term247 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))))).
Definition term307 := Nat.add (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term99 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term302 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term193 (x0 : int) (x1 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (real_le (real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)).
Definition term440 (x0 : nat) (x1 : nat) := @COND nat (@IN nat (S (Nat.add x0 x1)) (dotdot x0 (Nat.add x0 x1))) (@CARD nat (dotdot x0 (Nat.add x0 x1))) (S (@CARD nat (dotdot x0 (Nat.add x0 x1)))).
Definition term82 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term451 (x0 : nat) (x1 : nat) := and (Peano.le x0 (S (Nat.add x0 x1))).
Definition term113 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term352 (x0 : nat) := S (NUMERAL x0).
Definition term419 (x0 : nat) (x1 : nat) := dotdot x0 (S x1).
Definition term429 (x0 : nat) := forall y0 : nat, (Nat.add (S x0) y0) = (S (Nat.add x0 y0)).
Definition term22 (x0 : int) := ~ (~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term232 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT0 (BIT1 0)))))).
Definition term44 (x0 : int) := real_add (real_of_int x0) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term77 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term411 (x0 : nat) := forall y0 : nat, @FINITE nat (dotdot x0 y0).
Definition term351 (x0 : nat) := (fun y0 : nat => (S (NUMERAL y0)) = (NUMERAL (S y0))) x0.
Definition term138 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term135 (x0 : int) := and (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term325 (x0 : nat) := imp (((fun y0 : nat => (@CARD nat (dotdot x0 (Nat.add x0 y0))) = (Nat.add y0 (NUMERAL (BIT1 0)))) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (@CARD nat (dotdot x0 (Nat.add x0 y1))) = (Nat.add y1 (NUMERAL (BIT1 0)))) y0) -> (fun y1 : nat => (@CARD nat (dotdot x0 (Nat.add x0 y1))) = (Nat.add y1 (NUMERAL (BIT1 0)))) (S y0))).
Definition term52 (x0 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term432 (x0 : nat) (x1 : nat) := dotdot x0 (Nat.add x0 (S x1)).
Definition term69 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term368 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term292 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term142 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term86 (x0 : int) := real_sub (real_of_int x0) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term300 (x0 : nat) (x1 : nat) := (int_le (int_of_num (NUMERAL 0)) (int_of_num x0)) -> (int_le (int_of_num (NUMERAL 0)) (int_of_num x1)) -> int_le (int_of_num x1) (int_add (int_of_num x0) (int_add (int_of_num x1) (int_of_num (NUMERAL (BIT1 0))))).
Definition term207 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term116 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term217 := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term203 := real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term109 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term165 (x0 : nat) (x1 : nat) := int_le (int_of_num x1) (int_add (int_of_num x0) (int_add (int_of_num x1) (int_of_num (NUMERAL (BIT1 0))))).
Definition term241 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))).
Definition term81 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term405 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (@IN nat y1 (dotdot x0 y0)) = ((Peano.le x0 y1) /\ (Peano.le y1 y0))) x1.
Definition term214 := Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term154 (x0 : nat) (x1 : nat) := Peano.le x0 (S (Nat.add x0 x1)).
Definition term161 (x0 : nat) (x1 : nat) := int_add (int_of_num x0) (int_of_num (Nat.add x1 (NUMERAL (BIT1 0)))).
Definition term311 (x0 : nat) (x1 : nat) := @CARD nat (dotdot x0 (Nat.add x0 x1)).
Definition term412 (x0 : nat) (x1 : nat) := (fun y0 : nat => @FINITE nat (dotdot x0 y0)) x1.
Definition term169 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) /\ (~ (int_le x1 (int_add x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0))))))).
Definition term37 := real_le (real_of_num (NUMERAL 0)).
Definition term321 (x0 : nat) := forall y0 : nat, ((fun y1 : nat => (@CARD nat (dotdot x0 (Nat.add x0 y1))) = (Nat.add y1 (NUMERAL (BIT1 0)))) y0) -> (fun y1 : nat => (@CARD nat (dotdot x0 (Nat.add x0 y1))) = (Nat.add y1 (NUMERAL (BIT1 0)))) (S y0).
Definition term41 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term145 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term337 := (forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)))).
Definition term189 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term231 (x0 : int) (x1 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT0 (BIT1 0)))))).
Definition term259 := real_lt (real_of_num (NUMERAL 0)).
Definition term48 (x0 : int) := real_add (real_of_int x0).
Definition term18 (x0 : nat) := (fun y0 : nat => int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) x0.
Definition term316 (x0 : nat) := Nat.add (S x0) (NUMERAL (BIT1 0)).
Definition term195 (x0 : int) (x1 : int) := ~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (real_le (real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))))).
Definition term366 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term235 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term147 := and ((NUMERAL 0) = (NUMERAL 0)).
Definition term392 := False -> (@CARD nat (@EMPTY nat)) = (NUMERAL 0).
Definition term308 (x0 : nat) := and ((fun y0 : nat => (@CARD nat (dotdot x0 (Nat.add x0 y0))) = (Nat.add y0 (NUMERAL (BIT1 0)))) (NUMERAL 0)).
Definition term338 := (forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))).
Definition term105 (x0 : int) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term33 (x0 : nat) := real_of_int (int_of_num x0).
Definition term124 := real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term136 (x0 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term120 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term76 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term176 (x0 : int) (x1 : int) := int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1.
Definition term199 (x0 : int) := real_add (real_of_int x0) (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term42 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term430 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (S x0) y0) = (S (Nat.add x0 y0))) x1.
Definition term396 := NUMERAL (S 0).
Definition term107 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term68 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term393 (x0 : nat) (x1 : nat) := (False -> (@CARD nat (@EMPTY nat)) = (NUMERAL 0)) -> ((~ False) -> (S (@CARD nat (@EMPTY nat))) = x1) -> (@COND nat (@IN nat x0 (@EMPTY nat)) (@CARD nat (@EMPTY nat)) (S (@CARD nat (@EMPTY nat)))) = (@COND nat False (NUMERAL 0) x1).
Definition term319 (x0 : nat) := fun y0 : nat => ((fun y1 : nat => (@CARD nat (dotdot x0 (Nat.add x0 y1))) = (Nat.add y1 (NUMERAL (BIT1 0)))) y0) -> (fun y1 : nat => (@CARD nat (dotdot x0 (Nat.add x0 y1))) = (Nat.add y1 (NUMERAL (BIT1 0)))) (S y0).
Definition term295 := ((NUMERAL 0) = (NUMERAL 0)) /\ ((NUMERAL (BIT0 (BIT1 0))) = (NUMERAL 0)).
Definition term146 := ((NUMERAL 0) = (NUMERAL 0)) /\ ((NUMERAL (BIT1 0)) = (NUMERAL 0)).
Definition term243 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term97 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term439 (x0 : nat) (x1 : nat) := @FINITE nat (dotdot x0 (Nat.add x0 x1)).
Definition term171 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ (~ ((int_le (int_of_num (NUMERAL 0)) x1) -> int_le x1 (int_add x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0))))))).
Definition term257 (x0 : int) (x1 : int) := (real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0)))).
Definition term371 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term112 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term254 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))))).
Definition term164 (x0 : nat) := int_le (int_of_num x0).
Definition term222 := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL (BIT1 0)).
Definition term152 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term446 (x0 : nat) (x1 : nat) (x2 : Prop) (x3 : nat) := (fun y0 : nat => forall y1 : nat, ((@IN nat (S (Nat.add x0 x1)) (dotdot x0 (Nat.add x0 x1))) = x2) -> (x2 -> (@CARD nat (dotdot x0 (Nat.add x0 x1))) = y0) -> ((~ x2) -> (S (@CARD nat (dotdot x0 (Nat.add x0 x1)))) = y1) -> (@COND nat (@IN nat (S (Nat.add x0 x1)) (dotdot x0 (Nat.add x0 x1))) (@CARD nat (dotdot x0 (Nat.add x0 x1))) (S (@CARD nat (dotdot x0 (Nat.add x0 x1))))) = (@COND nat x2 y0 y1)) x3.
Definition term26 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x0).
Definition term283 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0).
Definition term359 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@CARD a0 (@INSERT a0 x0 y0)) = (@COND nat (@IN a0 x0 y0) (@CARD a0 y0) (S (@CARD a0 y0))).
Definition term251 (x0 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term324 (x0 : nat) := ((@CARD nat (dotdot x0 (Nat.add x0 (NUMERAL 0)))) = (Nat.add (NUMERAL 0) (NUMERAL (BIT1 0)))) /\ (forall y0 : nat, ((@CARD nat (dotdot x0 (Nat.add x0 y0))) = (Nat.add y0 (NUMERAL (BIT1 0)))) -> (@CARD nat (dotdot x0 (Nat.add x0 (S y0)))) = (Nat.add (S y0) (NUMERAL (BIT1 0)))).
Definition term464 := forall y0 : nat, forall y1 : nat, (@CARD nat (dotdot y0 (Nat.add y0 y1))) = (Nat.add y1 (NUMERAL (BIT1 0))).
Definition term445 (x0 : nat) (x1 : nat) (x2 : Prop) := forall y0 : nat, forall y1 : nat, ((@IN nat (S (Nat.add x0 x1)) (dotdot x0 (Nat.add x0 x1))) = x2) -> (x2 -> (@CARD nat (dotdot x0 (Nat.add x0 x1))) = y0) -> ((~ x2) -> (S (@CARD nat (dotdot x0 (Nat.add x0 x1)))) = y1) -> (@COND nat (@IN nat (S (Nat.add x0 x1)) (dotdot x0 (Nat.add x0 x1))) (@CARD nat (dotdot x0 (Nat.add x0 x1))) (S (@CARD nat (dotdot x0 (Nat.add x0 x1))))) = (@COND nat x2 y0 y1).
Definition term427 := forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1)).
Definition term422 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term404 (x0 : nat) := forall y0 : nat, forall y1 : nat, (@IN nat y1 (dotdot x0 y0)) = ((Peano.le x0 y1) /\ (Peano.le y1 y0)).
Definition term385 (x0 : nat) (x1 : Prop) := forall y0 : nat, forall y1 : nat, ((@IN nat x0 (@EMPTY nat)) = x1) -> (x1 -> (@CARD nat (@EMPTY nat)) = y0) -> ((~ x1) -> (S (@CARD nat (@EMPTY nat))) = y1) -> (@COND nat (@IN nat x0 (@EMPTY nat)) (@CARD nat (@EMPTY nat)) (S (@CARD nat (@EMPTY nat)))) = (@COND nat x1 y0 y1).
Definition term344 := forall y0 : nat, forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1).
Definition term340 := forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1).
Definition term242 := real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term318 (x0 : nat) (x1 : nat) := ((@CARD nat (dotdot x0 (Nat.add x0 x1))) = (Nat.add x1 (NUMERAL (BIT1 0)))) -> (@CARD nat (dotdot x0 (Nat.add x0 (S x1)))) = (Nat.add (S x1) (NUMERAL (BIT1 0))).
Definition term129 (x0 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term51 (x0 : int) := real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term182 (x0 : int) (x1 : int) := real_of_int (int_add (int_add x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0))))) (int_of_num (NUMERAL (BIT1 0)))).
Definition term94 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term17 (x0 : nat) := ~ (int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x0)).
Definition term315 (x0 : nat) (x1 : nat) := @CARD nat (dotdot x0 (Nat.add x0 (S x1))).
Definition term386 (x0 : nat) (x1 : Prop) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((@IN nat x0 (@EMPTY nat)) = x1) -> (x1 -> (@CARD nat (@EMPTY nat)) = y0) -> ((~ x1) -> (S (@CARD nat (@EMPTY nat))) = y1) -> (@COND nat (@IN nat x0 (@EMPTY nat)) (@CARD nat (@EMPTY nat)) (S (@CARD nat (@EMPTY nat)))) = (@COND nat x1 y0 y1)) x2.
Definition term194 (x0 : int) (x1 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (real_le (real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1))).
Definition term29 (x0 : int) := ~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x0).
Definition term269 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term457 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ False) -> (S (@CARD nat (dotdot x0 (Nat.add x0 x1)))) = x2) -> (@COND nat (@IN nat (S (Nat.add x0 x1)) (dotdot x0 (Nat.add x0 x1))) (@CARD nat (dotdot x0 (Nat.add x0 x1))) (S (@CARD nat (dotdot x0 (Nat.add x0 x1))))) = (@COND nat False (Nat.add x1 (NUMERAL (BIT1 0))) x2).
Definition term281 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))))) (real_of_int x0).
Definition term278 (x0 : real) (x1 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term267 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term156 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x0 x1).
Definition term219 := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term391 (x0 : nat) (x1 : nat) (x2 : nat) := (False -> (@CARD nat (@EMPTY nat)) = x1) -> ((~ False) -> (S (@CARD nat (@EMPTY nat))) = x2) -> (@COND nat (@IN nat x0 (@EMPTY nat)) (@CARD nat (@EMPTY nat)) (S (@CARD nat (@EMPTY nat)))) = (@COND nat False x1 x2).
Definition term330 (x0 : nat) := (((@CARD nat (dotdot x0 (Nat.add x0 (NUMERAL 0)))) = (Nat.add (NUMERAL 0) (NUMERAL (BIT1 0)))) /\ (forall y0 : nat, ((@CARD nat (dotdot x0 (Nat.add x0 y0))) = (Nat.add y0 (NUMERAL (BIT1 0)))) -> (@CARD nat (dotdot x0 (Nat.add x0 (S y0)))) = (Nat.add (S y0) (NUMERAL (BIT1 0))))) -> forall y0 : nat, (@CARD nat (dotdot x0 (Nat.add x0 y0))) = (Nat.add y0 (NUMERAL (BIT1 0))).
Definition term363 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @COND nat (@IN a0 x0 x1) (@CARD a0 x1) (S (@CARD a0 x1)).
Definition term163 (x0 : nat) (x1 : nat) := int_add (int_of_num x0) (int_add (int_of_num x1) (int_of_num (NUMERAL (BIT1 0)))).
Definition term244 := real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term98 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term159 (x0 : nat) (x1 : nat) := int_le (int_of_num x1) (int_of_num (Nat.add x0 (Nat.add x1 (NUMERAL (BIT1 0))))).
Definition term369 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term376 (x0 : nat) := @COND nat (@IN nat x0 (@EMPTY nat)) (@CARD nat (@EMPTY nat)) (S (@CARD nat (@EMPTY nat))).
Definition term312 (x0 : nat) (x1 : nat) := imp ((fun y0 : nat => (@CARD nat (dotdot x0 (Nat.add x0 y0))) = (Nat.add y0 (NUMERAL (BIT1 0)))) x1).
Definition term370 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term73 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term286 := real_ge (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term133 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term0 (x0 : nat) := Nat.add x0 (NUMERAL (BIT1 0)).
Definition term132 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))))).
Definition term221 := Nat.mul (BIT0 (BIT1 0)) (BIT1 0).
Definition term285 (x0 : int) := real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))))) (real_of_int x0)).
Definition term263 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term291 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term141 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term433 (x0 : nat) (x1 : nat) := dotdot x0 (S (Nat.add x0 x1)).
Definition term40 (x0 : int) := int_add x0 (int_of_num (NUMERAL (BIT1 0))).
Definition term220 := real_of_num (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL (BIT1 0))).
Definition term277 (x0 : int) := (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term160 (x0 : nat) (x1 : nat) := int_of_num (Nat.add x0 (Nat.add x1 (NUMERAL (BIT1 0)))).
Definition term114 := S (Nat.add 0 0).
Definition term66 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term388 (x0 : nat) (x1 : Prop) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((@IN nat x0 (@EMPTY nat)) = x1) -> (x1 -> (@CARD nat (@EMPTY nat)) = x2) -> ((~ x1) -> (S (@CARD nat (@EMPTY nat))) = y0) -> (@COND nat (@IN nat x0 (@EMPTY nat)) (@CARD nat (@EMPTY nat)) (S (@CARD nat (@EMPTY nat)))) = (@COND nat x1 x2 y0)) x3.
Definition term406 (x0 : nat) (x1 : nat) := forall y0 : nat, (@IN nat y0 (dotdot x0 x1)) = ((Peano.le x0 y0) /\ (Peano.le y0 x1)).
Definition term162 (x0 : nat) := int_add (int_of_num x0).
Definition term64 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term205 := real_of_num (NUMERAL (BIT0 (BIT1 0))).
Definition term293 := real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term91 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term463 (x0 : nat) := @eq nat (S (Nat.add x0 (NUMERAL (BIT1 0)))).
Definition term271 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)).
Definition term12 (x0 : nat) := int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0))).
Definition term266 (x0 : int) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term225 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term449 (x0 : nat) (x1 : nat) (x2 : Prop) (x3 : nat) (x4 : nat) := ((@IN nat (S (Nat.add x0 x1)) (dotdot x0 (Nat.add x0 x1))) = x2) -> (x2 -> (@CARD nat (dotdot x0 (Nat.add x0 x1))) = x3) -> ((~ x2) -> (S (@CARD nat (dotdot x0 (Nat.add x0 x1)))) = x4) -> (@COND nat (@IN nat (S (Nat.add x0 x1)) (dotdot x0 (Nat.add x0 x1))) (@CARD nat (dotdot x0 (Nat.add x0 x1))) (S (@CARD nat (dotdot x0 (Nat.add x0 x1))))) = (@COND nat x2 x3 x4).
Definition term425 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0))) x1.
Definition term299 (x0 : int) (x1 : int) := ~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (real_le (real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))).
Definition term122 := real_mul (real_of_num (NUMERAL 0)).
Definition term201 := real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term441 (x0 : nat) (x1 : nat) := forall y0 : Prop, forall y1 : nat, forall y2 : nat, ((@IN nat (S (Nat.add x0 x1)) (dotdot x0 (Nat.add x0 x1))) = y0) -> (y0 -> (@CARD nat (dotdot x0 (Nat.add x0 x1))) = y1) -> ((~ y0) -> (S (@CARD nat (dotdot x0 (Nat.add x0 x1)))) = y2) -> (@COND nat (@IN nat (S (Nat.add x0 x1)) (dotdot x0 (Nat.add x0 x1))) (@CARD nat (dotdot x0 (Nat.add x0 x1))) (S (@CARD nat (dotdot x0 (Nat.add x0 x1))))) = (@COND nat y0 y1 y2).
Definition term382 (x0 : nat) := forall y0 : Prop, forall y1 : nat, forall y2 : nat, ((@IN nat x0 (@EMPTY nat)) = y0) -> (y0 -> (@CARD nat (@EMPTY nat)) = y1) -> ((~ y0) -> (S (@CARD nat (@EMPTY nat))) = y2) -> (@COND nat (@IN nat x0 (@EMPTY nat)) (@CARD nat (@EMPTY nat)) (S (@CARD nat (@EMPTY nat)))) = (@COND nat y0 y1 y2).
Definition term381 (x0 : Prop) (x1 : nat) (x2 : nat) := forall y0 : Prop, forall y1 : nat, forall y2 : nat, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND nat x0 x1 x2) = (@COND nat y0 y1 y2).
Definition term380 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := forall y0 : Prop, forall y1 : a0, forall y2 : a0, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND a0 x0 x1 x2) = (@COND a0 y0 y1 y2).
Definition term365 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term215 := NUMERAL (BIT0 (BIT1 0)).
Definition term50 (x0 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))).
Definition term174 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> int_le x1 (int_add x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0))))).
Definition term227 (x0 : int) := real_sub (real_of_int x0).
Definition term19 (x0 : nat) := int_le (int_of_num (NUMERAL 0)) (int_of_num x0).
Definition term71 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term198 (x0 : int) := real_add (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term229 (x0 : int) (x1 : int) := real_sub (real_of_int x1) (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT0 (BIT1 0)))))).
Definition term126 := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term413 (x0 : nat) (x1 : nat) := @FINITE nat (dotdot x0 x1).
Definition term90 := real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term228 (x0 : int) (x1 : int) := real_sub (real_of_int x1) (real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term273 (x0 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))))) (real_of_num (NUMERAL 0)).
Definition term24 (x0 : int) := and (int_le (int_of_num (NUMERAL 0)) x0).
Definition term375 (x0 : nat) := (@FINITE nat (@EMPTY nat)) -> (@CARD nat (@INSERT nat x0 (@EMPTY nat))) = (@COND nat (@IN nat x0 (@EMPTY nat)) (@CARD nat (@EMPTY nat)) (S (@CARD nat (@EMPTY nat)))).
Definition term212 := Nat.add (BIT1 0) (BIT1 0).
Definition term54 (x0 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term248 (x0 : int) (x1 : int) := real_add (real_of_int x1) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))))).
Definition term95 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term401 := @eq nat (NUMERAL (BIT1 0)).
Definition term58 (x0 : int) := real_sub (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term30 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term428 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) x0.
Definition term423 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))) x0.
Definition term414 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 (S y1)) -> (dotdot y0 (S y1)) = (@INSERT nat (S y1) (dotdot y0 y1))) x0.
Definition term345 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((NUMERAL y0) = (NUMERAL y1)) = (y0 = y1)) x0.
Definition term341 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1)) x0.
Definition term350 := forall y0 : nat, (S (NUMERAL y0)) = (NUMERAL (S y0)).
Definition term255 (x0 : int) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0)).
Definition term459 (x0 : nat) (x1 : nat) := (~ False) -> (S (@CARD nat (dotdot x0 (Nat.add x0 x1)))) = (S (Nat.add x1 (NUMERAL (BIT1 0)))).
Definition term438 (x0 : nat) (x1 : nat) := dotdot x0 (Nat.add x0 x1).
Definition term409 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x1) /\ (Peano.le x1 x2).
Definition term56 (x0 : int) := ~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)))).
Definition term249 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_of_int x1) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))))).
Definition term434 (x0 : nat) (x1 : nat) := (Peano.le x0 (S (Nat.add x0 x1))) -> (dotdot x0 (S (Nat.add x0 x1))) = (@INSERT nat (S (Nat.add x0 x1)) (dotdot x0 (Nat.add x0 x1))).
Definition term407 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (@IN nat y0 (dotdot x0 x1)) = ((Peano.le x0 y0) /\ (Peano.le y0 x1))) x2.
Definition term78 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term279 (x0 : int) := ((real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0)))) -> real_ge (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term268 (x0 : int) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_of_int x0) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0)) (real_of_num (NUMERAL 0)).
Definition term59 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term379 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) := forall y0 : a0, forall y1 : a0, (x0 = x3) -> (x3 -> x1 = y0) -> ((~ x3) -> x2 = y1) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 y0 y1).
Definition term384 (x0 : nat) (x1 : Prop) := (fun y0 : Prop => forall y1 : nat, forall y2 : nat, ((@IN nat x0 (@EMPTY nat)) = y0) -> (y0 -> (@CARD nat (@EMPTY nat)) = y1) -> ((~ y0) -> (S (@CARD nat (@EMPTY nat))) = y2) -> (@COND nat (@IN nat x0 (@EMPTY nat)) (@CARD nat (@EMPTY nat)) (S (@CARD nat (@EMPTY nat)))) = (@COND nat y0 y1 y2)) x1.
Definition term3 (x0 : nat) := Peano.le (S x0) x0.
Definition term373 (x0 : nat) := @CARD nat (@INSERT nat x0 (@EMPTY nat)).
Definition term74 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term80 (x0 : real) := real_div x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term125 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term47 := real_of_num (NUMERAL (BIT1 0)).
Definition term264 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term4 (x0 : nat) := Peano.le (Nat.add x0 (NUMERAL (BIT1 0))) x0.
Definition term320 (x0 : nat) := fun y0 : nat => ((@CARD nat (dotdot x0 (Nat.add x0 y0))) = (Nat.add y0 (NUMERAL (BIT1 0)))) -> (@CARD nat (dotdot x0 (Nat.add x0 (S y0)))) = (Nat.add (S y0) (NUMERAL (BIT1 0))).
Definition term213 := BIT0 (BIT1 0).
Definition term31 (x0 : int) := real_le (real_of_int (int_of_num (NUMERAL 0))) (real_of_int x0).
Definition term426 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term252 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term131 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term443 (x0 : nat) (x1 : nat) := S (@CARD nat (dotdot x0 (Nat.add x0 x1))).
Definition term5 (x0 : nat) := ~ (Peano.le (S x0) x0).
Definition term53 (x0 : int) := and (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)).
Definition term276 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))))).
Definition term275 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))))).
Definition term398 (x0 : nat) := ((~ False) -> (S (@CARD nat (@EMPTY nat))) = (NUMERAL (BIT1 0))) -> (@COND nat (@IN nat x0 (@EMPTY nat)) (@CARD nat (@EMPTY nat)) (S (@CARD nat (@EMPTY nat)))) = (@COND nat False (NUMERAL 0) (NUMERAL (BIT1 0))).
Definition term200 := real_add (real_of_num (NUMERAL (BIT1 0))).
Definition term177 (x0 : int) (x1 : int) := ~ (int_le x1 (int_add x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))).
Definition term453 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((@IN nat (S (Nat.add x0 x1)) (dotdot x0 (Nat.add x0 x1))) = False) -> (False -> (@CARD nat (dotdot x0 (Nat.add x0 x1))) = x2) -> ((~ False) -> (S (@CARD nat (dotdot x0 (Nat.add x0 x1)))) = x3) -> (@COND nat (@IN nat (S (Nat.add x0 x1)) (dotdot x0 (Nat.add x0 x1))) (@CARD nat (dotdot x0 (Nat.add x0 x1))) (S (@CARD nat (dotdot x0 (Nat.add x0 x1))))) = (@COND nat False x2 x3).
Definition term240 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0))).
Definition term246 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term100 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term223 := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term326 (x0 : nat) := imp (((@CARD nat (dotdot x0 (Nat.add x0 (NUMERAL 0)))) = (Nat.add (NUMERAL 0) (NUMERAL (BIT1 0)))) /\ (forall y0 : nat, ((@CARD nat (dotdot x0 (Nat.add x0 y0))) = (Nat.add y0 (NUMERAL (BIT1 0)))) -> (@CARD nat (dotdot x0 (Nat.add x0 (S y0)))) = (Nat.add (S y0) (NUMERAL (BIT1 0))))).
Definition term410 (x0 : nat) := (fun y0 : nat => forall y1 : nat, @FINITE nat (dotdot y0 y1)) x0.
Definition term238 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0))))).
Definition term304 (x0 : nat) := fun y0 : nat => (@CARD nat (dotdot x0 (Nat.add x0 y0))) = (Nat.add y0 (NUMERAL (BIT1 0))).
Definition term290 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term262 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term140 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term167 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x1) -> int_le x1 (int_add x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0))))).
Definition term356 (a0 : Type') (x0 : a0) := (~ (@IN a0 x0 (@EMPTY a0))) -> (@IN a0 x0 (@EMPTY a0)) = False.
Definition term442 (x0 : nat) (x1 : nat) := @IN nat (S (Nat.add x0 x1)) (dotdot x0 (Nat.add x0 x1)).
Definition term168 (x0 : int) (x1 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) x1) -> int_le x1 (int_add x0 (int_add x1 (int_of_num (NUMERAL (BIT1 0)))))).
Definition term282 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term230 (x0 : int) (x1 : int) := real_add (real_of_int x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT0 (BIT1 0))))))).
Definition term211 := real_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term270 (x0 : int) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_int x0).
Definition term7 (x0 : nat) (x1 : nat) := int_le (int_of_num x0) (int_of_num x1).
Definition term46 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term72 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term455 (x0 : nat) (x1 : nat) := False -> (@CARD nat (dotdot x0 (Nat.add x0 x1))) = (Nat.add x1 (NUMERAL (BIT1 0))).
Definition term1 (x0 : nat) := Peano.le (S x0).
Definition term334 := (forall y0 : nat, ((BIT1 y0) = 0) = False) /\ ((forall y0 : nat, (0 = (BIT0 y0)) = (0 = y0)) /\ ((forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))))).
Definition term415 (x0 : nat) := forall y0 : nat, (Peano.le x0 (S y0)) -> (dotdot x0 (S y0)) = (@INSERT nat (S y0) (dotdot x0 y0)).
Definition term322 (x0 : nat) := forall y0 : nat, ((@CARD nat (dotdot x0 (Nat.add x0 y0))) = (Nat.add y0 (NUMERAL (BIT1 0)))) -> (@CARD nat (dotdot x0 (Nat.add x0 (S y0)))) = (Nat.add (S y0) (NUMERAL (BIT1 0))).
Definition term400 (x0 : nat) := @eq nat (@CARD nat (dotdot x0 (Nat.add x0 (NUMERAL 0)))).
Definition term348 := (forall y0 : nat, (S (NUMERAL y0)) = (NUMERAL (S y0))) /\ (((S 0) = (BIT1 0)) /\ ((forall y0 : nat, (S (BIT0 y0)) = (BIT1 y0)) /\ (forall y0 : nat, (S (BIT1 y0)) = (BIT0 (S y0))))).
Definition term437 (x0 : nat) (x1 : nat) := (@FINITE nat (dotdot x0 (Nat.add x0 x1))) -> (@CARD nat (@INSERT nat (S (Nat.add x0 x1)) (dotdot x0 (Nat.add x0 x1)))) = (@COND nat (@IN nat (S (Nat.add x0 x1)) (dotdot x0 (Nat.add x0 x1))) (@CARD nat (dotdot x0 (Nat.add x0 x1))) (S (@CARD nat (dotdot x0 (Nat.add x0 x1))))).
Definition term11 (x0 : nat) := int_of_num (Nat.add x0 (NUMERAL (BIT1 0))).
Definition term28 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term2 (x0 : nat) := Peano.le (Nat.add x0 (NUMERAL (BIT1 0))).
Definition term197 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_add (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term49 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term209 := real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term9 (x0 : nat) (x1 : nat) := int_of_num (Nat.add x0 x1).
Definition term153 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x0 x1) (NUMERAL (BIT1 0)).
Definition term128 (x0 : int) := real_mul (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term329 (x0 : nat) := forall y0 : nat, (@CARD nat (dotdot x0 (Nat.add x0 y0))) = (Nat.add y0 (NUMERAL (BIT1 0))).
Definition term233 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term88 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term310 (x0 : nat) (x1 : nat) := (fun y0 : nat => (@CARD nat (dotdot x0 (Nat.add x0 y0))) = (Nat.add y0 (NUMERAL (BIT1 0)))) x1.
Definition term399 := @COND nat False (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term305 (x0 : nat) := (fun y0 : nat => (@CARD nat (dotdot x0 (Nat.add x0 y0))) = (Nat.add y0 (NUMERAL (BIT1 0)))) (NUMERAL 0).
Definition term185 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int (int_add x1 (int_of_num (NUMERAL (BIT1 0))))).
Definition term260 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term108 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term60 (x0 : nat) := real_div (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term36 := real_le (real_of_int (int_of_num (NUMERAL 0))).
Definition term287 := real_ge (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term134 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term417 (x0 : nat) (x1 : nat) := (Peano.le x0 (S x1)) -> (dotdot x0 (S x1)) = (@INSERT nat (S x1) (dotdot x0 x1)).
Definition term301 (x0 : nat) (x1 : nat) := (int_le (int_of_num (NUMERAL 0)) (int_of_num x1)) -> int_le (int_of_num x1) (int_add (int_of_num x0) (int_add (int_of_num x1) (int_of_num (NUMERAL (BIT1 0))))).
Definition term67 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term347 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((NUMERAL x0) = (NUMERAL y0)) = (x0 = y0)) x1.
Definition term343 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((BIT1 x0) = (BIT1 y0)) = (x0 = y0)) x1.
Definition term309 (x0 : nat) := and ((@CARD nat (dotdot x0 (Nat.add x0 (NUMERAL 0)))) = (Nat.add (NUMERAL 0) (NUMERAL (BIT1 0)))).
Definition term79 := real_div (real_of_num (NUMERAL 0)).
Definition term130 := real_add (real_of_num (NUMERAL 0)).
Definition term418 (x0 : nat) (x1 : nat) := Peano.le x0 (S x1).
Definition term357 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@CARD a0 (@INSERT a0 y0 y1)) = (@COND nat (@IN a0 y0 y1) (@CARD a0 y1) (S (@CARD a0 y1))).
Definition term297 (x0 : int) (x1 : int) := (~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ (real_le (real_add (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)))))) -> False.
Definition term148 (x0 : int) := (~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))))) -> False.
Definition term389 (x0 : nat) (x1 : Prop) (x2 : nat) (x3 : nat) := ((@IN nat x0 (@EMPTY nat)) = x1) -> (x1 -> (@CARD nat (@EMPTY nat)) = x2) -> ((~ x1) -> (S (@CARD nat (@EMPTY nat))) = x3) -> (@COND nat (@IN nat x0 (@EMPTY nat)) (@CARD nat (@EMPTY nat)) (S (@CARD nat (@EMPTY nat)))) = (@COND nat x1 x2 x3).
Definition term377 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) (x5 : a0) := (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = x5) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 x5).
Definition term157 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.add x1 (NUMERAL (BIT1 0))).
Definition term218 := real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term123 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term45 := int_of_num (NUMERAL (BIT1 0)).
Definition term239 := Nat.mul (BIT1 0) (BIT0 (BIT1 0)).
Definition term431 (x0 : nat) (x1 : nat) := Nat.add (S x0) x1.
Definition term284 (x0 : int) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_of_int x0)).
Definition term39 (x0 : int) := real_le (real_of_int (int_add x0 (int_of_num (NUMERAL (BIT1 0))))) (real_of_int x0).
Definition term14 (x0 : nat) := int_le (int_of_num (Nat.add x0 (NUMERAL (BIT1 0)))).
Definition term10 (x0 : nat) (x1 : nat) := int_add (int_of_num x0) (int_of_num x1).
Definition term27 (x0 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) x0) -> ~ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term336 := (forall y0 : nat, (0 = (BIT1 y0)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT0 y1)) = (y0 = y1)) /\ ((forall y0 : nat, forall y1 : nat, ((BIT0 y0) = (BIT1 y1)) = False) /\ ((forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT0 y1)) = False) /\ (forall y0 : nat, forall y1 : nat, ((BIT1 y0) = (BIT1 y1)) = (y0 = y1))))).
Definition term13 := NUMERAL (BIT1 0).
Definition term461 (x0 : nat) := @COND nat False (Nat.add x0 (NUMERAL (BIT1 0))) (S (Nat.add x0 (NUMERAL (BIT1 0)))).
Definition term258 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term150 (x0 : int) := ~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_le (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term237 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term93 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term354 (a0 : Type') (x0 : a0) := (fun y0 : a0 => ~ (@IN a0 y0 (@EMPTY a0))) x0.
Definition term8 (x0 : nat) := int_le (int_of_num (Nat.add x0 (NUMERAL (BIT1 0)))) (int_of_num x0).
Definition term274 (x0 : int) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))))) (real_of_num (NUMERAL 0)).
Definition term265 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term462 (x0 : nat) (x1 : nat) := @eq nat (@CARD nat (dotdot x0 (Nat.add x0 (S x1)))).
Definition term57 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term151 (x0 : nat) := (int_le (int_of_num (NUMERAL 0)) (int_of_num x0)) -> ~ (int_le (int_add (int_of_num x0) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num x0)).
Definition term424 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
