Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term26 (a0 : Type') (x0 : nat) := fun y0 : a0 -> Prop => (@nsum a0 y0 (fun y1 : a0 => x0)) = (Nat.mul (@CARD a0 y0) x0).
Definition term280 (x0 : int) (x1 : int) := real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term126 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : Prop) (x3 : nat) (x4 : nat) := (fun y0 : nat => ((@IN a0 x0 x1) = x2) -> (x2 -> (@CARD a0 x1) = x3) -> ((~ x2) -> (S (@CARD a0 x1)) = y0) -> (@COND nat (@IN a0 x0 x1) (@CARD a0 x1) (S (@CARD a0 x1))) = (@COND nat x2 x3 y0)) x4.
Definition term7 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> nat, forall y2 : a0 -> Prop, (@FINITE a0 y2) -> (@nsum a0 (@INSERT a0 y0 y2) y1) = (@COND nat (@IN a0 y0 y2) (@nsum a0 y2 y1) (Nat.add (y1 y0) (@nsum a0 y2 y1))).
Definition term339 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term63 (a0 : Type') (x0 : nat) := fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@nsum a0 y0 (fun y1 : a0 => x0)) = (Nat.mul (@CARD a0 y0) x0).
Definition term225 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term155 := real_le (real_of_int (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_of_num (NUMERAL 0))).
Definition term187 (x0 : nat) := real_div (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term199 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term322 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term165 := real_add (real_of_int (int_of_num (NUMERAL 0))).
Definition term255 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := int_le (int_of_num (NUMERAL 0)) (int_of_num (Nat.mul x0 (@CARD a0 x1))).
Definition term236 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := Nat.mul (Nat.add (@CARD a0 x0) (NUMERAL (BIT1 0))) x1.
Definition term217 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term67 (a0 : Type') (x0 : nat) := fun y0 : a0 => x0.
Definition term308 (x0 : int) (x1 : int) := real_sub (real_add (real_of_int x0) (real_of_int x1)) (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term332 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term144 (a0 : Type') (x0 : nat) := fun y0 : a0 => forall y1 : a0 -> Prop, (((@nsum a0 y1 (fun y2 : a0 => x0)) = (Nat.mul (@CARD a0 y1) x0)) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> (Nat.add x0 (Nat.mul (@CARD a0 y1) x0)) = (Nat.mul (S (@CARD a0 y1)) x0).
Definition term52 (a0 : Type') (x0 : nat) := fun y0 : a0 => forall y1 : a0 -> Prop, (((@nsum a0 y1 (fun y2 : a0 => x0)) = (Nat.mul (@CARD a0 y1) x0)) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> (@nsum a0 (@INSERT a0 y0 y1) (fun y2 : a0 => x0)) = (Nat.mul (@CARD a0 (@INSERT a0 y0 y1)) x0).
Definition term97 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) (x3 : Prop) (x4 : nat) := (fun y0 : nat => forall y1 : nat, ((@IN a0 x0 x1) = x3) -> (x3 -> (@nsum a0 x1 (fun y2 : a0 => x2)) = y0) -> ((~ x3) -> (Nat.add ((fun y2 : a0 => x2) x0) (@nsum a0 x1 (fun y2 : a0 => x2))) = y1) -> (@COND nat (@IN a0 x0 x1) (@nsum a0 x1 (fun y2 : a0 => x2)) (Nat.add ((fun y2 : a0 => x2) x0) (@nsum a0 x1 (fun y2 : a0 => x2)))) = (@COND nat x3 y0 y1)) x4.
Definition term333 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term59 (a0 : Type') (x0 : a0 -> Prop) := imp (@FINITE a0 x0).
Definition term69 := @eq nat (NUMERAL 0).
Definition term186 (x0 : nat) := real_neg (real_of_num x0).
Definition term125 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : Prop) (x3 : nat) := forall y0 : nat, ((@IN a0 x0 x1) = x2) -> (x2 -> (@CARD a0 x1) = x3) -> ((~ x2) -> (S (@CARD a0 x1)) = y0) -> (@COND nat (@IN a0 x0 x1) (@CARD a0 x1) (S (@CARD a0 x1))) = (@COND nat x2 x3 y0).
Definition term98 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) (x3 : Prop) (x4 : nat) := forall y0 : nat, ((@IN a0 x0 x1) = x3) -> (x3 -> (@nsum a0 x1 (fun y1 : a0 => x2)) = x4) -> ((~ x3) -> (Nat.add ((fun y1 : a0 => x2) x0) (@nsum a0 x1 (fun y1 : a0 => x2))) = y0) -> (@COND nat (@IN a0 x0 x1) (@nsum a0 x1 (fun y1 : a0 => x2)) (Nat.add ((fun y1 : a0 => x2) x0) (@nsum a0 x1 (fun y1 : a0 => x2)))) = (@COND nat x3 x4 y0).
Definition term250 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @eq int (int_of_num (Nat.add (Nat.mul x1 (@CARD a0 x0)) x1)).
Definition term163 := real_of_int (int_of_num (NUMERAL 0)).
Definition term177 (x0 : Prop) := ~ (~ x0).
Definition term164 := real_of_num (NUMERAL 0).
Definition term343 (x0 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term129 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) (x3 : nat) := (False -> (@CARD a0 x1) = x2) -> ((~ False) -> (S (@CARD a0 x1)) = x3) -> (@COND nat (@IN a0 x0 x1) (@CARD a0 x1) (S (@CARD a0 x1))) = (@COND nat False x2 x3).
Definition term306 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))).
Definition term156 := int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))).
Definition term132 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := ((~ False) -> (S (@CARD a0 x1)) = x2) -> (@COND nat (@IN a0 x0 x1) (@CARD a0 x1) (S (@CARD a0 x1))) = (@COND nat False (@CARD a0 x1) x2).
Definition term283 (x0 : int) (x1 : int) := or (real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_int x1))).
Definition term122 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : Prop) := (fun y0 : Prop => forall y1 : nat, forall y2 : nat, ((@IN a0 x0 x1) = y0) -> (y0 -> (@CARD a0 x1) = y1) -> ((~ y0) -> (S (@CARD a0 x1)) = y2) -> (@COND nat (@IN a0 x0 x1) (@CARD a0 x1) (S (@CARD a0 x1))) = (@COND nat y0 y1 y2)) x2.
Definition term147 := int_of_num (NUMERAL 0).
Definition term173 := real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term257 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> (int_le (int_of_num (NUMERAL 0)) x0) -> (int_add x0 x1) = (int_add x0 x1).
Definition term150 (x0 : int) (x1 : int) := (int_le (int_add x1 (int_of_num (NUMERAL (BIT1 0)))) x0) \/ (int_le (int_add x0 (int_of_num (NUMERAL (BIT1 0)))) x1).
Definition term118 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := @eq nat (@nsum a0 (@INSERT a0 x0 x1) (fun y0 : a0 => x2)).
Definition term349 (x0 : int) (x1 : int) := ((~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_int x1))) \/ (real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_int x1)))))))) -> False) -> ~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_int x1))) \/ (real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_int x1)))))).
Definition term331 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term335 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term278 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))).
Definition term321 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term28 (a0 : Type') (x0 : nat) := @nsum a0 (@EMPTY a0) (fun y0 : a0 => x0).
Definition term14 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) := @nsum a0 (@INSERT a0 x0 x1) x2.
Definition term215 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term48 (a0 : Type') (x0 : a0) (x1 : nat) := fun y0 : a0 -> Prop => (((@nsum a0 y0 (fun y1 : a0 => x1)) = (Nat.mul (@CARD a0 y0) x1)) /\ ((~ (@IN a0 x0 y0)) /\ (@FINITE a0 y0))) -> (@nsum a0 (@INSERT a0 x0 y0) (fun y1 : a0 => x1)) = (Nat.mul (@CARD a0 (@INSERT a0 x0 y0)) x1).
Definition term5 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @CARD a0 (@INSERT a0 x0 x1).
Definition term256 (x0 : int) (x1 : int) := ~ (~ ((int_le (int_of_num (NUMERAL 0)) x1) -> (int_le (int_of_num (NUMERAL 0)) x0) -> (int_add x0 x1) = (int_add x0 x1))).
Definition term296 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term352 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := int_of_num (Nat.mul x0 (@CARD a0 x1)).
Definition term193 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term269 (x0 : int) (x1 : int) := ~ ((int_add x0 x1) = (int_add x0 x1)).
Definition term234 (a0 : Type') (x0 : a0 -> Prop) := Nat.add (@CARD a0 x0) (NUMERAL (BIT1 0)).
Definition term232 := ~ ((real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term324 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term45 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : a0 -> Prop) := (((fun y0 : a0 -> Prop => (@nsum a0 y0 (fun y1 : a0 => x0)) = (Nat.mul (@CARD a0 y0) x0)) x2) /\ ((~ (@IN a0 x1 x2)) /\ (@FINITE a0 x2))) -> (fun y0 : a0 -> Prop => (@nsum a0 y0 (fun y1 : a0 => x0)) = (Nat.mul (@CARD a0 y0) x0)) (@INSERT a0 x1 x2).
Definition term108 (a0 : Type') (x0 : nat) (x1 : a0) := (fun y0 : a0 => (fun y1 : a0 => x0) y0) x1.
Definition term241 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := Nat.add (Nat.mul x0 (@CARD a0 x1)).
Definition term82 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := ((((@nsum a0 x2 (fun y0 : a0 => x0)) = (Nat.mul (@CARD a0 x2) x0)) /\ ((~ (@IN a0 x1 x2)) /\ (@FINITE a0 x2))) = (((@nsum a0 x2 (fun y0 : a0 => x0)) = (Nat.mul (@CARD a0 x2) x0)) /\ ((~ (@IN a0 x1 x2)) /\ (@FINITE a0 x2)))) -> ((((@nsum a0 x2 (fun y0 : a0 => x0)) = (Nat.mul (@CARD a0 x2) x0)) /\ ((~ (@IN a0 x1 x2)) /\ (@FINITE a0 x2))) -> ((@nsum a0 (@INSERT a0 x1 x2) (fun y0 : a0 => x0)) = (Nat.mul (@CARD a0 (@INSERT a0 x1 x2)) x0)) = x3) -> ((((@nsum a0 x2 (fun y0 : a0 => x0)) = (Nat.mul (@CARD a0 x2) x0)) /\ ((~ (@IN a0 x1 x2)) /\ (@FINITE a0 x2))) -> (@nsum a0 (@INSERT a0 x1 x2) (fun y0 : a0 => x0)) = (Nat.mul (@CARD a0 (@INSERT a0 x1 x2)) x0)) = ((((@nsum a0 x2 (fun y0 : a0 => x0)) = (Nat.mul (@CARD a0 x2) x0)) /\ ((~ (@IN a0 x1 x2)) /\ (@FINITE a0 x2))) -> x3).
Definition term304 (x0 : int) := real_ge (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term231 := ((~ (~ ((real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))))) -> False) -> ~ ((real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term264 (x0 : int) (x1 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) x1) -> (int_le (int_of_num (NUMERAL 0)) x0) -> (int_add x0 x1) = (int_add x0 x1)).
Definition term152 := (int_le (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0))) \/ (int_le (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0))).
Definition term3 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@CARD a0 (@INSERT a0 x0 y0)) = (@COND nat (@IN a0 x0 y0) (@CARD a0 y0) (S (@CARD a0 y0)))) x1.
Definition term170 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term342 (x0 : int) := real_add (real_of_int x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term114 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := Nat.add x1 (Nat.mul (@CARD a0 x0) x1).
Definition term29 (a0 : Type') (x0 : nat) := Nat.mul (@CARD a0 (@EMPTY a0)) x0.
Definition term89 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) := forall y0 : a0, (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = y0) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 y0).
Definition term174 := or (int_le (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0))).
Definition term226 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_neg (real_of_num x1)).
Definition term329 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term328 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term315 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term212 := real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term4 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> (@CARD a0 (@INSERT a0 x0 x1)) = (@COND nat (@IN a0 x0 x1) (@CARD a0 x1) (S (@CARD a0 x1))).
Definition term268 (x0 : int) := real_le (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term83 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : a0 -> Prop) (x3 : Prop) := ((((@nsum a0 x2 (fun y0 : a0 => x0)) = (Nat.mul (@CARD a0 x2) x0)) /\ ((~ (@IN a0 x1 x2)) /\ (@FINITE a0 x2))) -> ((@nsum a0 (@INSERT a0 x1 x2) (fun y0 : a0 => x0)) = (Nat.mul (@CARD a0 (@INSERT a0 x1 x2)) x0)) = x3) -> ((((@nsum a0 x2 (fun y0 : a0 => x0)) = (Nat.mul (@CARD a0 x2) x0)) /\ ((~ (@IN a0 x1 x2)) /\ (@FINITE a0 x2))) -> (@nsum a0 (@INSERT a0 x1 x2) (fun y0 : a0 => x0)) = (Nat.mul (@CARD a0 (@INSERT a0 x1 x2)) x0)) = ((((@nsum a0 x2 (fun y0 : a0 => x0)) = (Nat.mul (@CARD a0 x2) x0)) /\ ((~ (@IN a0 x1 x2)) /\ (@FINITE a0 x2))) -> x3).
Definition term237 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := Nat.mul x0 (Nat.add (@CARD a0 x1) (NUMERAL (BIT1 0))).
Definition term303 (x0 : int) := real_ge (real_of_int x0).
Definition term51 (a0 : Type') (x0 : nat) := fun y0 : a0 => forall y1 : a0 -> Prop, (((fun y2 : a0 -> Prop => (@nsum a0 y2 (fun y3 : a0 => x0)) = (Nat.mul (@CARD a0 y2) x0)) y1) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> (fun y2 : a0 -> Prop => (@nsum a0 y2 (fun y3 : a0 => x0)) = (Nat.mul (@CARD a0 y2) x0)) (@INSERT a0 y0 y1).
Definition term84 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ~ (@IN a0 x0 x1).
Definition term203 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term111 (a0 : Type') (x0 : nat) (x1 : a0) := @eq nat ((fun y0 : a0 => (fun y1 : a0 => x0) y0) x1).
Definition term178 := ~ (~ ((real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))))).
Definition term151 := ~ ((int_of_num (NUMERAL 0)) = (int_of_num (NUMERAL 0))).
Definition term189 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term134 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := ((~ False) -> (S (@CARD a0 x1)) = (S (@CARD a0 x1))) -> (@COND nat (@IN a0 x0 x1) (@CARD a0 x1) (S (@CARD a0 x1))) = (@COND nat False (@CARD a0 x1) (S (@CARD a0 x1))).
Definition term104 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) (x3 : nat) := (False -> (@nsum a0 x1 (fun y0 : a0 => x2)) = (Nat.mul (@CARD a0 x1) x2)) -> ((~ False) -> (Nat.add ((fun y0 : a0 => x2) x0) (@nsum a0 x1 (fun y0 : a0 => x2))) = x3) -> (@COND nat (@IN a0 x0 x1) (@nsum a0 x1 (fun y0 : a0 => x2)) (Nat.add ((fun y0 : a0 => x2) x0) (@nsum a0 x1 (fun y0 : a0 => x2)))) = (@COND nat False (Nat.mul (@CARD a0 x1) x2) x3).
Definition term262 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) /\ (~ ((int_le (int_of_num (NUMERAL 0)) x0) -> (int_add x0 x1) = (int_add x0 x1))).
Definition term154 := int_le (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))) (int_of_num (NUMERAL 0)).
Definition term274 (x0 : int) (x1 : int) := real_of_int (int_add (int_add x0 x1) (int_of_num (NUMERAL (BIT1 0)))).
Definition term211 := real_le (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term181 := real_sub (real_of_num (NUMERAL 0)) (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term117 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @COND nat False (Nat.mul (@CARD a0 x0) x1) (Nat.add x1 (Nat.mul (@CARD a0 x0) x1)).
Definition term1 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@CARD a0 (@INSERT a0 y0 y1)) = (@COND nat (@IN a0 y0 y1) (@CARD a0 y1) (S (@CARD a0 y1)))) x0.
Definition term318 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term282 (x0 : int) (x1 : int) := or (int_le (int_add (int_add x0 x1) (int_of_num (NUMERAL (BIT1 0)))) (int_add x0 x1)).
Definition term316 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)).
Definition term302 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term219 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term347 (x0 : int) (x1 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_of_int x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))).
Definition term312 (x0 : int) (x1 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term297 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term214 := real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term345 (x0 : int) := and (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))).
Definition term78 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((((@nsum a0 x1 (fun y2 : a0 => x2)) = (Nat.mul (@CARD a0 x1) x2)) /\ ((~ (@IN a0 x0 x1)) /\ (@FINITE a0 x1))) = y0) -> (y0 -> ((@nsum a0 (@INSERT a0 x0 x1) (fun y2 : a0 => x2)) = (Nat.mul (@CARD a0 (@INSERT a0 x0 x1)) x2)) = y1) -> ((((@nsum a0 x1 (fun y2 : a0 => x2)) = (Nat.mul (@CARD a0 x1) x2)) /\ ((~ (@IN a0 x0 x1)) /\ (@FINITE a0 x1))) -> (@nsum a0 (@INSERT a0 x0 x1) (fun y2 : a0 => x2)) = (Nat.mul (@CARD a0 (@INSERT a0 x0 x1)) x2)) = (y0 -> y1)) x3.
Definition term254 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := (fun y0 : nat => int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) (Nat.mul x0 (@CARD a0 x1)).
Definition term295 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term38 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : a0 -> Prop) := ((fun y0 : a0 -> Prop => (@nsum a0 y0 (fun y1 : a0 => x0)) = (Nat.mul (@CARD a0 y0) x0)) x2) /\ ((~ (@IN a0 x1 x2)) /\ (@FINITE a0 x2)).
Definition term222 := real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term258 (x0 : int) (x1 : int) := ~ ((int_le (int_of_num (NUMERAL 0)) x0) -> (int_add x0 x1) = (int_add x0 x1)).
Definition term330 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term320 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))) (real_add (real_of_int x1) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term327 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term171 := real_le (real_of_int (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0))))).
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := and ((@nsum a0 x0 (fun y0 : a0 => x1)) = (Nat.mul (@CARD a0 x0) x1)).
Definition term353 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (int_le (int_of_num (NUMERAL 0)) (int_of_num (Nat.mul x1 (@CARD a0 x0)))) -> (int_add (int_of_num (Nat.mul x1 (@CARD a0 x0))) (int_of_num x1)) = (int_add (int_of_num (Nat.mul x1 (@CARD a0 x0))) (int_of_num x1)).
Definition term65 (a0 : Type') (x0 : nat) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@nsum a0 y0 (fun y1 : a0 => x0)) = (Nat.mul (@CARD a0 y0) x0).
Definition term301 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term10 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@nsum a0 (@INSERT a0 x0 y1) y0) = (@COND nat (@IN a0 x0 y1) (@nsum a0 y1 y0) (Nat.add (y0 x0) (@nsum a0 y1 y0)))) x1.
Definition term103 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := False -> (@nsum a0 x0 (fun y0 : a0 => x1)) = (Nat.mul (@CARD a0 x0) x1).
Definition term281 (x0 : int) (x1 : int) := real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_int x1)).
Definition term13 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) := (@FINITE a0 x1) -> (@nsum a0 (@INSERT a0 x0 x1) x2) = (@COND nat (@IN a0 x0 x1) (@nsum a0 x1 x2) (Nat.add (x2 x0) (@nsum a0 x1 x2))).
Definition term289 (x0 : int) (x1 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_int x1))).
Definition term213 := real_le (real_of_num (NUMERAL 0)).
Definition term157 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term227 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term140 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := ((((@nsum a0 x1 (fun y0 : a0 => x2)) = (Nat.mul (@CARD a0 x1) x2)) /\ ((~ (@IN a0 x0 x1)) /\ (@FINITE a0 x1))) -> ((@nsum a0 (@INSERT a0 x0 x1) (fun y0 : a0 => x2)) = (Nat.mul (@CARD a0 (@INSERT a0 x0 x1)) x2)) = ((Nat.add x2 (Nat.mul (@CARD a0 x1) x2)) = (Nat.mul (S (@CARD a0 x1)) x2))) -> ((((@nsum a0 x1 (fun y0 : a0 => x2)) = (Nat.mul (@CARD a0 x1) x2)) /\ ((~ (@IN a0 x0 x1)) /\ (@FINITE a0 x1))) -> (@nsum a0 (@INSERT a0 x0 x1) (fun y0 : a0 => x2)) = (Nat.mul (@CARD a0 (@INSERT a0 x0 x1)) x2)) = ((((@nsum a0 x1 (fun y0 : a0 => x2)) = (Nat.mul (@CARD a0 x1) x2)) /\ ((~ (@IN a0 x0 x1)) /\ (@FINITE a0 x1))) -> (Nat.add x2 (Nat.mul (@CARD a0 x1) x2)) = (Nat.mul (S (@CARD a0 x1)) x2)).
Definition term310 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_of_int x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0)))))).
Definition term311 (x0 : int) (x1 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term277 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_of_int x1)).
Definition term300 (x0 : int) := real_add (real_of_int x0).
Definition term252 (x0 : nat) := (fun y0 : nat => int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) x0.
Definition term146 (a0 : Type') (x0 : nat) := ((NUMERAL 0) = (Nat.mul (NUMERAL 0) x0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (((@nsum a0 y1 (fun y2 : a0 => x0)) = (Nat.mul (@CARD a0 y1) x0)) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> (Nat.add x0 (Nat.mul (@CARD a0 y1) x0)) = (Nat.mul (S (@CARD a0 y1)) x0)).
Definition term288 (x0 : int) (x1 : int) := ~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_int x1))) \/ (real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_int x1))))))).
Definition term249 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := int_add (int_of_num (Nat.mul x1 (@CARD a0 x0))) (int_of_num x1).
Definition term74 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term121 (a0 : Type') (x0 : a0 -> Prop) := S (@CARD a0 x0).
Definition term175 := or (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term229 := and ((NUMERAL 0) = (NUMERAL 0)).
Definition term25 (a0 : Type') (x0 : nat) := (((fun y0 : a0 -> Prop => (@nsum a0 y0 (fun y1 : a0 => x0)) = (Nat.mul (@CARD a0 y0) x0)) (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (((fun y2 : a0 -> Prop => (@nsum a0 y2 (fun y3 : a0 => x0)) = (Nat.mul (@CARD a0 y2) x0)) y1) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> (fun y2 : a0 -> Prop => (@nsum a0 y2 (fun y3 : a0 => x0)) = (Nat.mul (@CARD a0 y2) x0)) (@INSERT a0 y0 y1))) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (fun y1 : a0 -> Prop => (@nsum a0 y1 (fun y2 : a0 => x0)) = (Nat.mul (@CARD a0 y1) x0)) y0.
Definition term323 (x0 : int) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0).
Definition term94 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := Nat.add ((fun y0 : a0 => x2) x0) (@nsum a0 x1 (fun y0 : a0 => x2)).
Definition term162 (x0 : nat) := real_of_int (int_of_num x0).
Definition term27 (a0 : Type') (x0 : nat) := (fun y0 : a0 -> Prop => (@nsum a0 y0 (fun y1 : a0 => x0)) = (Nat.mul (@CARD a0 y0) x0)) (@EMPTY a0).
Definition term224 := real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term346 (x0 : int) := (real_ge (real_of_int x0) (real_of_num (NUMERAL 0))) /\ (real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term176 := (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term16 (a0 : Type') := forall y0 : a0 -> nat, (@nsum a0 (@EMPTY a0) y0) = (NUMERAL 0).
Definition term334 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term200 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term158 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term245 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @eq nat (Nat.add (Nat.mul x1 (@CARD a0 x0)) x1).
Definition term242 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := Nat.add (Nat.mul x1 (@CARD a0 x0)) x1.
Definition term325 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term128 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) (x3 : nat) := ((@IN a0 x0 x1) = False) -> (False -> (@CARD a0 x1) = x2) -> ((~ False) -> (S (@CARD a0 x1)) = x3) -> (@COND nat (@IN a0 x0 x1) (@CARD a0 x1) (S (@CARD a0 x1))) = (@COND nat False x2 x3).
Definition term101 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) (x3 : nat) (x4 : nat) := ((@IN a0 x0 x1) = False) -> (False -> (@nsum a0 x1 (fun y0 : a0 => x2)) = x3) -> ((~ False) -> (Nat.add ((fun y0 : a0 => x2) x0) (@nsum a0 x1 (fun y0 : a0 => x2))) = x4) -> (@COND nat (@IN a0 x0 x1) (@nsum a0 x1 (fun y0 : a0 => x2)) (Nat.add ((fun y0 : a0 => x2) x0) (@nsum a0 x1 (fun y0 : a0 => x2)))) = (@COND nat False x3 x4).
Definition term159 := real_of_int (int_add (int_of_num (NUMERAL 0)) (int_of_num (NUMERAL (BIT1 0)))).
Definition term294 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term319 (x0 : int) (x1 : int) := real_add (real_add (real_of_int x0) (real_of_int x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x1)) (real_neg (real_of_num (NUMERAL (BIT1 0)))))).
Definition term115 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := (~ False) -> (Nat.add ((fun y0 : a0 => x2) x0) (@nsum a0 x1 (fun y0 : a0 => x2))) = (Nat.add x2 (Nat.mul (@CARD a0 x1) x2)).
Definition term228 := ((NUMERAL 0) = (NUMERAL 0)) /\ ((NUMERAL (BIT1 0)) = (NUMERAL 0)).
Definition term204 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term180 := real_sub (real_of_num (NUMERAL 0)).
Definition term136 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := Nat.mul (@CARD a0 (@INSERT a0 x0 x1)).
Definition term218 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term309 (x0 : int) (x1 : int) := real_sub (real_add (real_of_int x0) (real_of_int x1)) (real_add (real_of_int x0) (real_add (real_of_int x1) (real_of_num (NUMERAL (BIT1 0))))).
Definition term106 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term112 (a0 : Type') (x0 : nat) (x1 : a0) := @eq nat ((fun y0 : a0 => x0) x1).
Definition term124 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : Prop) (x3 : nat) := (fun y0 : nat => forall y1 : nat, ((@IN a0 x0 x1) = x2) -> (x2 -> (@CARD a0 x1) = y0) -> ((~ x2) -> (S (@CARD a0 x1)) = y1) -> (@COND nat (@IN a0 x0 x1) (@CARD a0 x1) (S (@CARD a0 x1))) = (@COND nat x2 y0 y1)) x3.
Definition term66 (a0 : Type') (x0 : nat) := (((@nsum a0 (@EMPTY a0) (fun y0 : a0 => x0)) = (Nat.mul (@CARD a0 (@EMPTY a0)) x0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (((@nsum a0 y1 (fun y2 : a0 => x0)) = (Nat.mul (@CARD a0 y1) x0)) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> (@nsum a0 (@INSERT a0 y0 y1) (fun y2 : a0 => x0)) = (Nat.mul (@CARD a0 (@INSERT a0 y0 y1)) x0))) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@nsum a0 y0 (fun y1 : a0 => x0)) = (Nat.mul (@CARD a0 y0) x0).
Definition term81 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) (x3 : Prop) (x4 : Prop) := ((((@nsum a0 x1 (fun y0 : a0 => x2)) = (Nat.mul (@CARD a0 x1) x2)) /\ ((~ (@IN a0 x0 x1)) /\ (@FINITE a0 x1))) = x3) -> (x3 -> ((@nsum a0 (@INSERT a0 x0 x1) (fun y0 : a0 => x2)) = (Nat.mul (@CARD a0 (@INSERT a0 x0 x1)) x2)) = x4) -> ((((@nsum a0 x1 (fun y0 : a0 => x2)) = (Nat.mul (@CARD a0 x1) x2)) /\ ((~ (@IN a0 x0 x1)) /\ (@FINITE a0 x1))) -> (@nsum a0 (@INSERT a0 x0 x1) (fun y0 : a0 => x2)) = (Nat.mul (@CARD a0 (@INSERT a0 x0 x1)) x2)) = (x3 -> x4).
Definition term11 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@nsum a0 (@INSERT a0 x0 y0) x1) = (@COND nat (@IN a0 x0 y0) (@nsum a0 y0 x1) (Nat.add (x1 x0) (@nsum a0 y0 x1))).
Definition term2 (a0 : Type') (x0 : a0) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@CARD a0 (@INSERT a0 x0 y0)) = (@COND nat (@IN a0 x0 y0) (@CARD a0 y0) (S (@CARD a0 y0))).
Definition term85 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ (@IN a0 x0 x1)) -> (@IN a0 x0 x1) = False.
Definition term40 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : a0 -> Prop) := imp (((fun y0 : a0 -> Prop => (@nsum a0 y0 (fun y1 : a0 => x0)) = (Nat.mul (@CARD a0 y0) x0)) x2) /\ ((~ (@IN a0 x1 x2)) /\ (@FINITE a0 x2))).
Definition term109 (a0 : Type') (x0 : nat) (x1 : a0) := (fun y0 : a0 => x0) x1.
Definition term354 (a0 : Type') := forall y0 : nat, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@nsum a0 y1 (fun y2 : a0 => y0)) = (Nat.mul (@CARD a0 y1) y0).
Definition term123 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : Prop) := forall y0 : nat, forall y1 : nat, ((@IN a0 x0 x1) = x2) -> (x2 -> (@CARD a0 x1) = y0) -> ((~ x2) -> (S (@CARD a0 x1)) = y1) -> (@COND nat (@IN a0 x0 x1) (@CARD a0 x1) (S (@CARD a0 x1))) = (@COND nat x2 y0 y1).
Definition term96 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) (x3 : Prop) := forall y0 : nat, forall y1 : nat, ((@IN a0 x0 x1) = x3) -> (x3 -> (@nsum a0 x1 (fun y2 : a0 => x2)) = y0) -> ((~ x3) -> (Nat.add ((fun y2 : a0 => x2) x0) (@nsum a0 x1 (fun y2 : a0 => x2))) = y1) -> (@COND nat (@IN a0 x0 x1) (@nsum a0 x1 (fun y2 : a0 => x2)) (Nat.add ((fun y2 : a0 => x2) x0) (@nsum a0 x1 (fun y2 : a0 => x2)))) = (@COND nat x3 y0 y1).
Definition term46 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := (((@nsum a0 x1 (fun y0 : a0 => x2)) = (Nat.mul (@CARD a0 x1) x2)) /\ ((~ (@IN a0 x0 x1)) /\ (@FINITE a0 x1))) -> (@nsum a0 (@INSERT a0 x0 x1) (fun y0 : a0 => x2)) = (Nat.mul (@CARD a0 (@INSERT a0 x0 x1)) x2).
Definition term341 (x0 : int) := real_add (real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0))).
Definition term107 (a0 : Type') (x0 : a0 -> nat) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term243 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := Nat.mul x0 (@CARD a0 x1).
Definition term201 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term305 (x0 : int) (x1 : int) := real_ge (real_sub (real_add (real_of_int x0) (real_of_int x1)) (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term286 (x0 : int) (x1 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_int x1))) \/ (real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_int x1)))).
Definition term119 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @eq nat (Nat.add x1 (Nat.mul (@CARD a0 x0) x1)).
Definition term284 (x0 : int) (x1 : int) := (real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_int x1))) \/ (real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_int x1))).
Definition term35 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := and ((fun y0 : a0 -> Prop => (@nsum a0 y0 (fun y1 : a0 => x0)) = (Nat.mul (@CARD a0 y0) x0)) x1).
Definition term259 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) /\ (~ ((int_add x0 x1) = (int_add x0 x1))).
Definition term6 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := @COND nat (@IN a0 x0 x1) (@CARD a0 x1) (S (@CARD a0 x1)).
Definition term351 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (int_le (int_of_num (NUMERAL 0)) (int_of_num x1)) -> (int_le (int_of_num (NUMERAL 0)) (int_of_num (Nat.mul x1 (@CARD a0 x0)))) -> (int_add (int_of_num (Nat.mul x1 (@CARD a0 x0))) (int_of_num x1)) = (int_add (int_of_num (Nat.mul x1 (@CARD a0 x0))) (int_of_num x1)).
Definition term205 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term183 := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term86 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := (@FINITE a0 x1) -> (@nsum a0 (@INSERT a0 x0 x1) (fun y0 : a0 => x2)) = (@COND nat (@IN a0 x0 x1) (@nsum a0 x1 (fun y0 : a0 => x2)) (Nat.add ((fun y0 : a0 => x2) x0) (@nsum a0 x1 (fun y0 : a0 => x2)))).
Definition term113 (a0 : Type') (x0 : nat) (x1 : a0) := Nat.add ((fun y0 : a0 => x0) x1).
Definition term270 (x0 : int) (x1 : int) := (int_le (int_add (int_add x0 x1) (int_of_num (NUMERAL (BIT1 0)))) (int_add x0 x1)) \/ (int_le (int_add (int_add x0 x1) (int_of_num (NUMERAL (BIT1 0)))) (int_add x0 x1)).
Definition term273 (x0 : int) (x1 : int) := int_add (int_add x0 x1) (int_of_num (NUMERAL (BIT1 0))).
Definition term197 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term209 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term233 (x0 : nat) := Nat.add x0 (NUMERAL (BIT1 0)).
Definition term275 (x0 : int) (x1 : int) := real_add (real_of_int (int_add x0 x1)) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term12 (a0 : Type') (x0 : a0) (x1 : a0 -> nat) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@nsum a0 (@INSERT a0 x0 y0) x1) = (@COND nat (@IN a0 x0 y0) (@nsum a0 y0 x1) (Nat.add (x1 x0) (@nsum a0 y0 x1)))) x2.
Definition term221 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term220 := S (Nat.add 0 0).
Definition term20 (a0 : Type') (x0 : type686 a0) := ((x0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, ((x0 y1) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> x0 (@INSERT a0 y0 y1))) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0.
Definition term190 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term188 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term62 (a0 : Type') (x0 : nat) := fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (fun y1 : a0 -> Prop => (@nsum a0 y1 (fun y2 : a0 => x0)) = (Nat.mul (@CARD a0 y1) x0)) y0.
Definition term137 (a0 : Type') (x0 : a0 -> Prop) := Nat.mul (S (@CARD a0 x0)).
Definition term192 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term61 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) -> (@nsum a0 x0 (fun y0 : a0 => x1)) = (Nat.mul (@CARD a0 x0) x1).
Definition term290 (x0 : int) (x1 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ (real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_int x1)))).
Definition term79 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) (x3 : Prop) := forall y0 : Prop, ((((@nsum a0 x1 (fun y1 : a0 => x2)) = (Nat.mul (@CARD a0 x1) x2)) /\ ((~ (@IN a0 x0 x1)) /\ (@FINITE a0 x1))) = x3) -> (x3 -> ((@nsum a0 (@INSERT a0 x0 x1) (fun y1 : a0 => x2)) = (Nat.mul (@CARD a0 (@INSERT a0 x0 x1)) x2)) = y0) -> ((((@nsum a0 x1 (fun y1 : a0 => x2)) = (Nat.mul (@CARD a0 x1) x2)) /\ ((~ (@IN a0 x0 x1)) /\ (@FINITE a0 x1))) -> (@nsum a0 (@INSERT a0 x0 x1) (fun y1 : a0 => x2)) = (Nat.mul (@CARD a0 (@INSERT a0 x0 x1)) x2)) = (x3 -> y0).
Definition term75 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term58 (a0 : Type') (x0 : nat) := imp (((@nsum a0 (@EMPTY a0) (fun y0 : a0 => x0)) = (Nat.mul (@CARD a0 (@EMPTY a0)) x0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (((@nsum a0 y1 (fun y2 : a0 => x0)) = (Nat.mul (@CARD a0 y1) x0)) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> (@nsum a0 (@INSERT a0 y0 y1) (fun y2 : a0 => x0)) = (Nat.mul (@CARD a0 (@INSERT a0 y0 y1)) x0))).
Definition term41 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : a0 -> Prop) := imp (((@nsum a0 x2 (fun y0 : a0 => x0)) = (Nat.mul (@CARD a0 x2) x0)) /\ ((~ (@IN a0 x1 x2)) /\ (@FINITE a0 x2))).
Definition term208 := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term344 (x0 : int) (x1 : int) := real_ge (real_sub (real_add (real_of_int x0) (real_of_int x1)) (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term49 (a0 : Type') (x0 : nat) (x1 : a0) := forall y0 : a0 -> Prop, (((fun y1 : a0 -> Prop => (@nsum a0 y1 (fun y2 : a0 => x0)) = (Nat.mul (@CARD a0 y1) x0)) y0) /\ ((~ (@IN a0 x1 y0)) /\ (@FINITE a0 y0))) -> (fun y1 : a0 -> Prop => (@nsum a0 y1 (fun y2 : a0 => x0)) = (Nat.mul (@CARD a0 y1) x0)) (@INSERT a0 x1 y0).
Definition term336 := real_mul (real_of_num (NUMERAL 0)).
Definition term120 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := forall y0 : Prop, forall y1 : nat, forall y2 : nat, ((@IN a0 x0 x1) = y0) -> (y0 -> (@CARD a0 x1) = y1) -> ((~ y0) -> (S (@CARD a0 x1)) = y2) -> (@COND nat (@IN a0 x0 x1) (@CARD a0 x1) (S (@CARD a0 x1))) = (@COND nat y0 y1 y2).
Definition term93 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := forall y0 : Prop, forall y1 : nat, forall y2 : nat, ((@IN a0 x0 x1) = y0) -> (y0 -> (@nsum a0 x1 (fun y3 : a0 => x2)) = y1) -> ((~ y0) -> (Nat.add ((fun y3 : a0 => x2) x0) (@nsum a0 x1 (fun y3 : a0 => x2))) = y2) -> (@COND nat (@IN a0 x0 x1) (@nsum a0 x1 (fun y3 : a0 => x2)) (Nat.add ((fun y3 : a0 => x2) x0) (@nsum a0 x1 (fun y3 : a0 => x2)))) = (@COND nat y0 y1 y2).
Definition term92 (x0 : Prop) (x1 : nat) (x2 : nat) := forall y0 : Prop, forall y1 : nat, forall y2 : nat, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND nat x0 x1 x2) = (@COND nat y0 y1 y2).
Definition term91 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) := forall y0 : Prop, forall y1 : a0, forall y2 : a0, (x0 = y0) -> (y0 -> x1 = y1) -> ((~ y0) -> x2 = y2) -> (@COND a0 x0 x1 x2) = (@COND a0 y0 y1 y2).
Definition term77 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := forall y0 : Prop, forall y1 : Prop, ((((@nsum a0 x1 (fun y2 : a0 => x2)) = (Nat.mul (@CARD a0 x1) x2)) /\ ((~ (@IN a0 x0 x1)) /\ (@FINITE a0 x1))) = y0) -> (y0 -> ((@nsum a0 (@INSERT a0 x0 x1) (fun y2 : a0 => x2)) = (Nat.mul (@CARD a0 (@INSERT a0 x0 x1)) x2)) = y1) -> ((((@nsum a0 x1 (fun y2 : a0 => x2)) = (Nat.mul (@CARD a0 x1) x2)) /\ ((~ (@IN a0 x0 x1)) /\ (@FINITE a0 x1))) -> (@nsum a0 (@INSERT a0 x0 x1) (fun y2 : a0 => x2)) = (Nat.mul (@CARD a0 (@INSERT a0 x0 x1)) x2)) = (y0 -> y1).
Definition term76 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := Nat.mul (@CARD a0 x0) x1.
Definition term179 := real_ge (real_sub (real_of_num (NUMERAL 0)) (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL 0)).
Definition term18 (a0 : Type') := forall y0 : type686 a0, ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, ((y0 y2) /\ ((~ (@IN a0 y1 y2)) /\ (@FINITE a0 y2))) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1.
Definition term9 (a0 : Type') (x0 : a0) := forall y0 : a0 -> nat, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@nsum a0 (@INSERT a0 x0 y1) y0) = (@COND nat (@IN a0 x0 y1) (@nsum a0 y1 y0) (Nat.add (y0 x0) (@nsum a0 y1 y0))).
Definition term253 (x0 : nat) := int_le (int_of_num (NUMERAL 0)) (int_of_num x0).
Definition term195 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term338 := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term80 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((((@nsum a0 x1 (fun y1 : a0 => x2)) = (Nat.mul (@CARD a0 x1) x2)) /\ ((~ (@IN a0 x0 x1)) /\ (@FINITE a0 x1))) = x3) -> (x3 -> ((@nsum a0 (@INSERT a0 x0 x1) (fun y1 : a0 => x2)) = (Nat.mul (@CARD a0 (@INSERT a0 x0 x1)) x2)) = y0) -> ((((@nsum a0 x1 (fun y1 : a0 => x2)) = (Nat.mul (@CARD a0 x1) x2)) /\ ((~ (@IN a0 x0 x1)) /\ (@FINITE a0 x1))) -> (@nsum a0 (@INSERT a0 x0 x1) (fun y1 : a0 => x2)) = (Nat.mul (@CARD a0 (@INSERT a0 x0 x1)) x2)) = (x3 -> y0)) x4.
Definition term172 := real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term149 (x0 : int) (x1 : int) := ~ (x0 = x1).
Definition term246 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := int_of_num (Nat.add (Nat.mul x1 (@CARD a0 x0)) x1).
Definition term185 := real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term39 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : a0 -> Prop) := ((@nsum a0 x2 (fun y0 : a0 => x0)) = (Nat.mul (@CARD a0 x2) x0)) /\ ((~ (@IN a0 x1 x2)) /\ (@FINITE a0 x2)).
Definition term261 (x0 : int) := and (int_le (int_of_num (NUMERAL 0)) x0).
Definition term15 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : a0 -> nat) := @COND nat (@IN a0 x0 x1) (@nsum a0 x1 x2) (Nat.add (x2 x0) (@nsum a0 x1 x2)).
Definition term235 (a0 : Type') (x0 : a0 -> Prop) := Nat.mul (Nat.add (@CARD a0 x0) (NUMERAL (BIT1 0))).
Definition term239 (x0 : nat) := Nat.mul x0 (NUMERAL (BIT1 0)).
Definition term32 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@nsum a0 y0 (fun y1 : a0 => x0)) = (Nat.mul (@CARD a0 y0) x0)) x1.
Definition term287 (x0 : int) (x1 : int) := (real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_int x1))) \/ (real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_int x1))))).
Definition term19 (a0 : Type') (x0 : type686 a0) := (fun y0 : type686 a0 => ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, ((y0 y2) /\ ((~ (@IN a0 y1 y2)) /\ (@FINITE a0 y2))) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1) x0.
Definition term44 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := Nat.mul (@CARD a0 (@INSERT a0 x0 x1)) x2.
Definition term202 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term17 (a0 : Type') (x0 : a0 -> nat) := (fun y0 : a0 -> nat => (@nsum a0 (@EMPTY a0) y0) = (NUMERAL 0)) x0.
Definition term141 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := (((@nsum a0 x1 (fun y0 : a0 => x2)) = (Nat.mul (@CARD a0 x1) x2)) /\ ((~ (@IN a0 x0 x1)) /\ (@FINITE a0 x1))) -> (Nat.add x2 (Nat.mul (@CARD a0 x1) x2)) = (Nat.mul (S (@CARD a0 x1)) x2).
Definition term292 (x0 : int) := real_sub (real_of_int x0) (real_of_num (NUMERAL 0)).
Definition term153 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term100 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) (x3 : Prop) (x4 : nat) (x5 : nat) := ((@IN a0 x0 x1) = x3) -> (x3 -> (@nsum a0 x1 (fun y0 : a0 => x2)) = x4) -> ((~ x3) -> (Nat.add ((fun y0 : a0 => x2) x0) (@nsum a0 x1 (fun y0 : a0 => x2))) = x5) -> (@COND nat (@IN a0 x0 x1) (@nsum a0 x1 (fun y0 : a0 => x2)) (Nat.add ((fun y0 : a0 => x2) x0) (@nsum a0 x1 (fun y0 : a0 => x2)))) = (@COND nat x3 x4 x5).
Definition term47 (a0 : Type') (x0 : nat) (x1 : a0) := fun y0 : a0 -> Prop => (((fun y1 : a0 -> Prop => (@nsum a0 y1 (fun y2 : a0 => x0)) = (Nat.mul (@CARD a0 y1) x0)) y0) /\ ((~ (@IN a0 x1 y0)) /\ (@FINITE a0 y0))) -> (fun y1 : a0 -> Prop => (@nsum a0 y1 (fun y2 : a0 => x0)) = (Nat.mul (@CARD a0 y1) x0)) (@INSERT a0 x1 y0).
Definition term133 (a0 : Type') (x0 : a0 -> Prop) := (~ False) -> (S (@CARD a0 x0)) = (S (@CARD a0 x0)).
Definition term68 (a0 : Type') (x0 : nat) := @eq nat (@nsum a0 (@EMPTY a0) (fun y0 : a0 => x0)).
Definition term298 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term22 (a0 : Type') (x0 : type686 a0) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0.
Definition term43 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := @nsum a0 (@INSERT a0 x0 x1) (fun y0 : a0 => x2).
Definition term293 (x0 : int) := real_add (real_of_int x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term90 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) := forall y0 : a0, forall y1 : a0, (x0 = x3) -> (x3 -> x1 = y0) -> ((~ x3) -> x2 = y1) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 y0 y1).
Definition term130 (a0 : Type') (x0 : a0 -> Prop) := False -> (@CARD a0 x0) = (@CARD a0 x0).
Definition term131 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := (False -> (@CARD a0 x1) = (@CARD a0 x1)) -> ((~ False) -> (S (@CARD a0 x1)) = x2) -> (@COND nat (@IN a0 x0 x1) (@CARD a0 x1) (S (@CARD a0 x1))) = (@COND nat False (@CARD a0 x1) x2).
Definition term198 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term138 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := Nat.mul (S (@CARD a0 x0)) x1.
Definition term206 (x0 : real) := real_div x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term223 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term168 := real_of_num (NUMERAL (BIT1 0)).
Definition term110 (a0 : Type') (x0 : nat) := fun y0 : a0 => (fun y1 : a0 => x0) y0.
Definition term350 (x0 : int) (x1 : int) := ~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_int x1))) \/ (real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_int x1)))))).
Definition term73 (x0 : nat) := and ((NUMERAL 0) = (Nat.mul (NUMERAL 0) x0)).
Definition term266 (x0 : int) := real_le (real_of_int (int_of_num (NUMERAL 0))) (real_of_int x0).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @nsum a0 x0 (fun y0 : a0 => x1).
Definition term30 (a0 : Type') (x0 : nat) := and ((fun y0 : a0 -> Prop => (@nsum a0 y0 (fun y1 : a0 => x0)) = (Nat.mul (@CARD a0 y0) x0)) (@EMPTY a0)).
Definition term207 := real_add (real_of_num (NUMERAL 0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term182 := real_sub (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term23 (a0 : Type') (x0 : type686 a0) := (forall y0 : type686 a0, ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, ((y0 y2) /\ ((~ (@IN a0 y1 y2)) /\ (@FINITE a0 y2))) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1) -> forall y0 : a0 -> Prop, (@FINITE a0 y0) -> x0 y0.
Definition term105 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) (x3 : nat) := ((~ False) -> (Nat.add ((fun y0 : a0 => x2) x0) (@nsum a0 x1 (fun y0 : a0 => x2))) = x3) -> (@COND nat (@IN a0 x0 x1) (@nsum a0 x1 (fun y0 : a0 => x2)) (Nat.add ((fun y0 : a0 => x2) x0) (@nsum a0 x1 (fun y0 : a0 => x2)))) = (@COND nat False (Nat.mul (@CARD a0 x1) x2) x3).
Definition term285 (x0 : int) := and (real_le (real_of_num (NUMERAL 0)) (real_of_int x0)).
Definition term263 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) /\ ((int_le (int_of_num (NUMERAL 0)) x0) /\ (~ ((int_add x0 x1) = (int_add x0 x1)))).
Definition term251 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := @eq int (int_add (int_of_num (Nat.mul x1 (@CARD a0 x0))) (int_of_num x1)).
Definition term317 (x0 : int) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_int x0)) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term216 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_le (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_le (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term139 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := (((@nsum a0 x1 (fun y0 : a0 => x2)) = (Nat.mul (@CARD a0 x1) x2)) /\ ((~ (@IN a0 x0 x1)) /\ (@FINITE a0 x1))) -> ((@nsum a0 (@INSERT a0 x0 x1) (fun y0 : a0 => x2)) = (Nat.mul (@CARD a0 (@INSERT a0 x0 x1)) x2)) = ((Nat.add x2 (Nat.mul (@CARD a0 x1) x2)) = (Nat.mul (S (@CARD a0 x1)) x2)).
Definition term167 := real_of_int (int_of_num (NUMERAL (BIT1 0))).
Definition term196 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term116 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := ((~ False) -> (Nat.add ((fun y0 : a0 => x2) x0) (@nsum a0 x1 (fun y0 : a0 => x2))) = (Nat.add x2 (Nat.mul (@CARD a0 x1) x2))) -> (@COND nat (@IN a0 x0 x1) (@nsum a0 x1 (fun y0 : a0 => x2)) (Nat.add ((fun y0 : a0 => x2) x0) (@nsum a0 x1 (fun y0 : a0 => x2)))) = (@COND nat False (Nat.mul (@CARD a0 x1) x2) (Nat.add x2 (Nat.mul (@CARD a0 x1) x2))).
Definition term71 := Nat.mul (NUMERAL 0).
Definition term72 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term127 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : Prop) (x3 : nat) (x4 : nat) := ((@IN a0 x0 x1) = x2) -> (x2 -> (@CARD a0 x1) = x3) -> ((~ x2) -> (S (@CARD a0 x1)) = x4) -> (@COND nat (@IN a0 x0 x1) (@CARD a0 x1) (S (@CARD a0 x1))) = (@COND nat x2 x3 x4).
Definition term260 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term24 (a0 : Type') := (forall y0 : type686 a0, ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, ((y0 y2) /\ ((~ (@IN a0 y1 y2)) /\ (@FINITE a0 y2))) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1) -> forall y0 : type686 a0, ((y0 (@EMPTY a0)) /\ (forall y1 : a0, forall y2 : a0 -> Prop, ((y0 y2) /\ ((~ (@IN a0 y1 y2)) /\ (@FINITE a0 y2))) -> y0 (@INSERT a0 y1 y2))) -> forall y1 : a0 -> Prop, (@FINITE a0 y1) -> y0 y1.
Definition term313 (x0 : int) := real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term31 (a0 : Type') (x0 : nat) := and ((@nsum a0 (@EMPTY a0) (fun y0 : a0 => x0)) = (Nat.mul (@CARD a0 (@EMPTY a0)) x0)).
Definition term247 (x0 : nat) (x1 : nat) := int_of_num (Nat.add x0 x1).
Definition term340 (x0 : int) := real_mul (real_of_num (NUMERAL 0)) (real_of_int x0).
Definition term265 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> (int_add x0 x1) = (int_add x0 x1).
Definition term314 (x0 : int) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_num (NUMERAL (BIT1 0)))).
Definition term143 (a0 : Type') (x0 : a0) (x1 : nat) := forall y0 : a0 -> Prop, (((@nsum a0 y0 (fun y1 : a0 => x1)) = (Nat.mul (@CARD a0 y0) x1)) /\ ((~ (@IN a0 x0 y0)) /\ (@FINITE a0 y0))) -> (Nat.add x1 (Nat.mul (@CARD a0 y0) x1)) = (Nat.mul (S (@CARD a0 y0)) x1).
Definition term50 (a0 : Type') (x0 : a0) (x1 : nat) := forall y0 : a0 -> Prop, (((@nsum a0 y0 (fun y1 : a0 => x1)) = (Nat.mul (@CARD a0 y0) x1)) /\ ((~ (@IN a0 x0 y0)) /\ (@FINITE a0 y0))) -> (@nsum a0 (@INSERT a0 x0 y0) (fun y1 : a0 => x1)) = (Nat.mul (@CARD a0 (@INSERT a0 x0 y0)) x1).
Definition term135 (a0 : Type') (x0 : a0 -> Prop) := @COND nat False (@CARD a0 x0) (S (@CARD a0 x0)).
Definition term272 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_add x0 x1) (int_of_num (NUMERAL (BIT1 0))))) (real_of_int (int_add x0 x1)).
Definition term307 (x0 : int) (x1 : int) := real_sub (real_add (real_of_int x0) (real_of_int x1)).
Definition term37 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) := (~ (@IN a0 x0 x1)) /\ (@FINITE a0 x1).
Definition term326 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term184 (x0 : nat) := real_div (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term42 (a0 : Type') (x0 : nat) (x1 : a0) (x2 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@nsum a0 y0 (fun y1 : a0 => x0)) = (Nat.mul (@CARD a0 y0) x0)) (@INSERT a0 x1 x2).
Definition term160 := real_add (real_of_int (int_of_num (NUMERAL 0))) (real_of_int (int_of_num (NUMERAL (BIT1 0)))).
Definition term267 := real_le (real_of_int (int_of_num (NUMERAL 0))).
Definition term210 := real_ge (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term191 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term276 (x0 : int) (x1 : int) := real_add (real_of_int (int_add x0 x1)).
Definition term56 (a0 : Type') (x0 : nat) := ((@nsum a0 (@EMPTY a0) (fun y0 : a0 => x0)) = (Nat.mul (@CARD a0 (@EMPTY a0)) x0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (((@nsum a0 y1 (fun y2 : a0 => x0)) = (Nat.mul (@CARD a0 y1) x0)) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> (@nsum a0 (@INSERT a0 y0 y1) (fun y2 : a0 => x0)) = (Nat.mul (@CARD a0 (@INSERT a0 y0 y1)) x0)).
Definition term299 := real_div (real_of_num (NUMERAL 0)).
Definition term95 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) (x3 : Prop) := (fun y0 : Prop => forall y1 : nat, forall y2 : nat, ((@IN a0 x0 x1) = y0) -> (y0 -> (@nsum a0 x1 (fun y3 : a0 => x2)) = y1) -> ((~ y0) -> (Nat.add ((fun y3 : a0 => x2) x0) (@nsum a0 x1 (fun y3 : a0 => x2))) = y2) -> (@COND nat (@IN a0 x0 x1) (@nsum a0 x1 (fun y3 : a0 => x2)) (Nat.add ((fun y3 : a0 => x2) x0) (@nsum a0 x1 (fun y3 : a0 => x2)))) = (@COND nat y0 y1 y2)) x3.
Definition term21 (a0 : Type') (x0 : type686 a0) := (x0 (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, ((x0 y1) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> x0 (@INSERT a0 y0 y1)).
Definition term166 := real_add (real_of_num (NUMERAL 0)).
Definition term145 (a0 : Type') (x0 : nat) := forall y0 : a0, forall y1 : a0 -> Prop, (((@nsum a0 y1 (fun y2 : a0 => x0)) = (Nat.mul (@CARD a0 y1) x0)) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> (Nat.add x0 (Nat.mul (@CARD a0 y1) x0)) = (Nat.mul (S (@CARD a0 y1)) x0).
Definition term54 (a0 : Type') (x0 : nat) := forall y0 : a0, forall y1 : a0 -> Prop, (((@nsum a0 y1 (fun y2 : a0 => x0)) = (Nat.mul (@CARD a0 y1) x0)) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> (@nsum a0 (@INSERT a0 y0 y1) (fun y2 : a0 => x0)) = (Nat.mul (@CARD a0 (@INSERT a0 y0 y1)) x0).
Definition term53 (a0 : Type') (x0 : nat) := forall y0 : a0, forall y1 : a0 -> Prop, (((fun y2 : a0 -> Prop => (@nsum a0 y2 (fun y3 : a0 => x0)) = (Nat.mul (@CARD a0 y2) x0)) y1) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> (fun y2 : a0 -> Prop => (@nsum a0 y2 (fun y3 : a0 => x0)) = (Nat.mul (@CARD a0 y2) x0)) (@INSERT a0 y0 y1).
Definition term0 (a0 : Type') := forall y0 : a0, forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@CARD a0 (@INSERT a0 y0 y1)) = (@COND nat (@IN a0 y0 y1) (@CARD a0 y1) (S (@CARD a0 y1))).
Definition term348 (x0 : int) (x1 : int) := (~ (~ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x1)) /\ ((real_le (real_of_num (NUMERAL 0)) (real_of_int x0)) /\ ((real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_int x1))) \/ (real_le (real_add (real_add (real_of_int x0) (real_of_int x1)) (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_of_int x0) (real_of_int x1)))))))) -> False.
Definition term230 := (~ (~ ((real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) \/ (real_le (real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)))))) -> False.
Definition term148 := ~ (~ ((int_of_num (NUMERAL 0)) = (int_of_num (NUMERAL 0)))).
Definition term57 (a0 : Type') (x0 : nat) := imp (((fun y0 : a0 -> Prop => (@nsum a0 y0 (fun y1 : a0 => x0)) = (Nat.mul (@CARD a0 y0) x0)) (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (((fun y2 : a0 -> Prop => (@nsum a0 y2 (fun y3 : a0 => x0)) = (Nat.mul (@CARD a0 y2) x0)) y1) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> (fun y2 : a0 -> Prop => (@nsum a0 y2 (fun y3 : a0 => x0)) = (Nat.mul (@CARD a0 y2) x0)) (@INSERT a0 y0 y1))).
Definition term279 (x0 : int) (x1 : int) := real_le (real_of_int (int_add (int_add x0 x1) (int_of_num (NUMERAL (BIT1 0))))).
Definition term88 (a0 : Type') (x0 : Prop) (x1 : a0) (x2 : a0) (x3 : Prop) (x4 : a0) (x5 : a0) := (x0 = x3) -> (x3 -> x1 = x4) -> ((~ x3) -> x2 = x5) -> (@COND a0 x0 x1 x2) = (@COND a0 x3 x4 x5).
Definition term8 (a0 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a0 -> nat, forall y2 : a0 -> Prop, (@FINITE a0 y2) -> (@nsum a0 (@INSERT a0 y0 y2) y1) = (@COND nat (@IN a0 y0 y2) (@nsum a0 y2 y1) (Nat.add (y1 y0) (@nsum a0 y2 y1)))) x0.
Definition term337 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term102 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) (x3 : nat) (x4 : nat) := (False -> (@nsum a0 x1 (fun y0 : a0 => x2)) = x3) -> ((~ False) -> (Nat.add ((fun y0 : a0 => x2) x0) (@nsum a0 x1 (fun y0 : a0 => x2))) = x4) -> (@COND nat (@IN a0 x0 x1) (@nsum a0 x1 (fun y0 : a0 => x2)) (Nat.add ((fun y0 : a0 => x2) x0) (@nsum a0 x1 (fun y0 : a0 => x2)))) = (@COND nat False x3 x4).
Definition term64 (a0 : Type') (x0 : nat) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (fun y1 : a0 -> Prop => (@nsum a0 y1 (fun y2 : a0 => x0)) = (Nat.mul (@CARD a0 y1) x0)) y0.
Definition term161 := int_of_num (NUMERAL (BIT1 0)).
Definition term87 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) := @COND nat (@IN a0 x0 x1) (@nsum a0 x1 (fun y0 : a0 => x2)) (Nat.add ((fun y0 : a0 => x2) x0) (@nsum a0 x1 (fun y0 : a0 => x2))).
Definition term99 (a0 : Type') (x0 : a0) (x1 : a0 -> Prop) (x2 : nat) (x3 : Prop) (x4 : nat) (x5 : nat) := (fun y0 : nat => ((@IN a0 x0 x1) = x3) -> (x3 -> (@nsum a0 x1 (fun y1 : a0 => x2)) = x4) -> ((~ x3) -> (Nat.add ((fun y1 : a0 => x2) x0) (@nsum a0 x1 (fun y1 : a0 => x2))) = y0) -> (@COND nat (@IN a0 x0 x1) (@nsum a0 x1 (fun y1 : a0 => x2)) (Nat.add ((fun y1 : a0 => x2) x0) (@nsum a0 x1 (fun y1 : a0 => x2)))) = (@COND nat x3 x4 y0)) x5.
Definition term248 (x0 : nat) (x1 : nat) := int_add (int_of_num x0) (int_of_num x1).
Definition term244 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := Nat.add x0 (Nat.mul x0 (@CARD a0 x1)).
Definition term169 := NUMERAL (BIT1 0).
Definition term240 (x0 : nat) := Nat.mul (NUMERAL (BIT1 0)) x0.
Definition term70 (a0 : Type') := Nat.mul (@CARD a0 (@EMPTY a0)).
Definition term194 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term142 (a0 : Type') (x0 : a0) (x1 : nat) := fun y0 : a0 -> Prop => (((@nsum a0 y0 (fun y1 : a0 => x1)) = (Nat.mul (@CARD a0 y0) x1)) /\ ((~ (@IN a0 x0 y0)) /\ (@FINITE a0 y0))) -> (Nat.add x1 (Nat.mul (@CARD a0 y0) x1)) = (Nat.mul (S (@CARD a0 y0)) x1).
Definition term238 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := Nat.add (Nat.mul x1 (@CARD a0 x0)) (Nat.mul x1 (NUMERAL (BIT1 0))).
Definition term55 (a0 : Type') (x0 : nat) := ((fun y0 : a0 -> Prop => (@nsum a0 y0 (fun y1 : a0 => x0)) = (Nat.mul (@CARD a0 y0) x0)) (@EMPTY a0)) /\ (forall y0 : a0, forall y1 : a0 -> Prop, (((fun y2 : a0 -> Prop => (@nsum a0 y2 (fun y3 : a0 => x0)) = (Nat.mul (@CARD a0 y2) x0)) y1) /\ ((~ (@IN a0 y0 y1)) /\ (@FINITE a0 y1))) -> (fun y2 : a0 -> Prop => (@nsum a0 y2 (fun y3 : a0 => x0)) = (Nat.mul (@CARD a0 y2) x0)) (@INSERT a0 y0 y1)).
Definition term60 (a0 : Type') (x0 : nat) (x1 : a0 -> Prop) := (@FINITE a0 x1) -> (fun y0 : a0 -> Prop => (@nsum a0 y0 (fun y1 : a0 => x0)) = (Nat.mul (@CARD a0 y0) x0)) x1.
Definition term291 (x0 : int) := real_ge (real_sub (real_of_int x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term271 (x0 : int) (x1 : int) := int_le (int_add (int_add x0 x1) (int_of_num (NUMERAL (BIT1 0)))) (int_add x0 x1).
