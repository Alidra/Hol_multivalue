Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term28 (x0 : real) := forall y0 : real, ((real_neg x0) = (real_neg y0)) = (x0 = y0).
Definition term657 (x0 : nat) (x1 : nat) := real_gt (real_sub (real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) (real_neg (real_of_num x1))).
Definition term532 (x0 : nat) (x1 : nat) := real_gt (real_sub (real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) (real_neg (real_of_num x1))).
Definition term79 := fun y0 : int => forall y1 : int, (real_of_int (int_add y0 y1)) = (real_add (real_of_int y0) (real_of_int y1)).
Definition term437 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term670 (x0 : nat) (x1 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1)) (real_of_num x1)).
Definition term401 (x0 : nat) := real_div (real_neg (real_of_num x0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term541 (x0 : nat) := ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL 0)))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term391 (x0 : nat) (x1 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1)).
Definition term420 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term445 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term409 (x0 : nat) (x1 : nat) := real_lt (real_of_num x0) (real_of_num x1).
Definition term426 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term722 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.add x0 x1).
Definition term452 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term746 (x0 : nat) (x1 : nat) := real_neg (real_add (real_of_num (Nat.add x1 x0)) (real_of_num x1)).
Definition term594 := real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term427 := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term631 (x0 : nat) := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0)) (real_of_num (NUMERAL 0))).
Definition term630 (x0 : nat) := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL 0))).
Definition term93 (x0 : nat) := real_neg (real_of_num x0).
Definition term408 := real_of_num (NUMERAL 0).
Definition term319 (x0 : nat) (x1 : nat) (x2 : nat) := or ((real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_of_num x1)) = (real_of_num x2)).
Definition term308 (x0 : nat) (x1 : nat) (x2 : nat) := or ((real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_of_num x2)).
Definition term91 (x0 : int) (x1 : int) (x2 : nat) := or ((real_add (real_of_int x0) (real_of_int x1)) = (real_of_num x2)).
Definition term47 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, ((exists y1 : a0, x0 y1) \/ (exists y1 : a0, y0 y1)) = (exists y1 : a0, (x0 y1) \/ (y0 y1)).
Definition term3 (a0 : Type') (x0 : a0) := exists y0 : a0, x0 = y0.
Definition term439 (x0 : nat) (x1 : nat) := real_sub (real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))).
Definition term392 (x0 : nat) (x1 : nat) := real_add (real_of_num x1) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1))).
Definition term487 := real_div (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term351 (x0 : nat) (x1 : nat) (x2 : nat) := ((real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num x2)) \/ ((real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_neg (real_of_num x2))).
Definition term287 (x0 : nat) (x1 : nat) (x2 : nat) := ((real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) = (real_of_num x2)) \/ ((real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) = (real_neg (real_of_num x2))).
Definition term223 (x0 : nat) (x1 : nat) (x2 : nat) := ((real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num x2)) \/ ((real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_neg (real_of_num x2))).
Definition term111 (x0 : int) (x1 : int) := @eq real (real_add (real_of_int x0) (real_of_int x1)).
Definition term733 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_of_num y0)) x2) \/ ((fun y0 : nat => (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))) x2).
Definition term701 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => (real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num y0)) x2) \/ ((fun y0 : nat => (real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_neg (real_of_num y0))) x2).
Definition term373 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_of_num y0)) x2) \/ ((fun y0 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))) x2).
Definition term342 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y0)) x2) \/ ((fun y0 : nat => (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y0))) x2).
Definition term309 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_of_num y0)) x2) \/ ((fun y0 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_neg (real_of_num y0))) x2).
Definition term278 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_of_num y0)) x2) \/ ((fun y0 : nat => (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_neg (real_of_num y0))) x2).
Definition term245 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_of_num y0)) x2) \/ ((fun y0 : nat => (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))) x2).
Definition term212 (x0 : nat) (x1 : nat) (x2 : nat) := ((fun y0 : nat => (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y0)) x2) \/ ((fun y0 : nat => (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y0))) x2).
Definition term94 (x0 : int) (x1 : int) (x2 : nat) := ((fun y0 : nat => (real_add (real_of_int x0) (real_of_int x1)) = (real_of_num y0)) x2) \/ ((fun y0 : nat => (real_add (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y0))) x2).
Definition term723 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add x0 (Nat.add x0 x1)) = y0.
Definition term76 (x0 : int) := fun y0 : int => exists y1 : nat, ((real_add (real_of_int x0) (real_of_int y0)) = (real_of_num y1)) \/ ((real_add (real_of_int x0) (real_of_int y0)) = (real_neg (real_of_num y1))).
Definition term301 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_neg (real_of_num y0))) x2.
Definition term92 (x0 : int) (x1 : int) (x2 : nat) := (fun y0 : nat => (real_add (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y0))) x2.
Definition term753 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (real_neg (real_of_num (Nat.add (Nat.add x1 x0) x1))) = (real_of_num y0)).
Definition term741 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_of_num y0)).
Definition term721 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (real_neg (real_of_num (Nat.add x0 (Nat.add x0 x1)))) = (real_of_num y0)).
Definition term709 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num y0)).
Definition term364 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_of_num y0)).
Definition term333 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y0)).
Definition term300 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_of_num y0)).
Definition term269 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_of_num y0)).
Definition term236 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_of_num y0)).
Definition term203 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y0)).
Definition term140 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_of_num y0)).
Definition term132 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num x1)) = (real_of_num y0)).
Definition term123 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (real_add (real_of_num x0) (real_neg (real_of_num x1))) = (real_of_num y0)).
Definition term104 (x0 : int) (x1 : int) := or (exists y0 : nat, (real_add (real_of_int x0) (real_of_int x1)) = (real_of_num y0)).
Definition term592 := ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term451 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term415 := ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term595 := real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term460 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term429 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))).
Definition term758 (x0 : nat) (x1 : nat) := fun y0 : nat => x0 = (Nat.add x1 y0).
Definition term602 (x0 : nat) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)).
Definition term37 (x0 : nat) := fun y0 : nat => (real_add (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.add x0 y0)).
Definition term553 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term745 (x0 : nat) (x1 : nat) := (exists y0 : nat, (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))).
Definition term713 (x0 : nat) (x1 : nat) := (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_neg (real_of_num y0))).
Definition term191 (x0 : nat) (x1 : nat) := (exists y0 : nat, (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))).
Definition term185 (x0 : nat) (x1 : nat) := (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y0))).
Definition term180 (x0 : nat) (x1 : nat) := (exists y0 : nat, (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_neg (real_of_num y0))).
Definition term174 (x0 : nat) (x1 : nat) := (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_neg (real_of_num y0))).
Definition term169 (x0 : nat) (x1 : nat) := (exists y0 : nat, (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))).
Definition term163 (x0 : nat) (x1 : nat) := (exists y0 : nat, (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y0))).
Definition term143 (x0 : nat) (x1 : nat) := (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))).
Definition term135 (x0 : nat) (x1 : nat) := (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num x1)) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num x1)) = (real_neg (real_of_num y0))).
Definition term126 (x0 : nat) (x1 : nat) := (exists y0 : nat, (real_add (real_of_num x0) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_of_num x0) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))).
Definition term108 (x0 : int) (x1 : int) := (exists y0 : nat, (real_add (real_of_int x0) (real_of_int x1)) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y0))).
Definition term36 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term394 (x0 : nat) := real_add (real_of_num x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)).
Definition term10 (x0 : real) := fun y0 : real => (real_neg (real_add x0 y0)) = (real_add (real_neg x0) (real_neg y0)).
Definition term158 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) -> (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))).
Definition term154 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) -> (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num x1)) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num x1)) = (real_neg (real_of_num y0))).
Definition term150 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) -> (exists y0 : nat, (real_add (real_of_num x0) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_of_num x0) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))).
Definition term678 (x0 : nat) (x1 : nat) := real_gt (real_sub (real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) (real_of_num x1)) (real_of_num (NUMERAL 0)).
Definition term648 (x0 : nat) (x1 : nat) := real_gt (real_sub (real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) (real_of_num x1)) (real_of_num (NUMERAL 0)).
Definition term576 (x0 : nat) (x1 : nat) := real_gt (real_sub (real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) (real_of_num x1)) (real_of_num (NUMERAL 0)).
Definition term498 (x0 : nat) (x1 : nat) := real_gt (real_sub (real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) (real_of_num x1)) (real_of_num (NUMERAL 0)).
Definition term599 := real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term359 (x0 : nat) (x1 : nat) := real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1)).
Definition term63 (x0 : int) := (fun y0 : int => forall y1 : int, (int_add y0 y1) = (int_of_real (real_add (real_of_int y0) (real_of_int y1)))) x0.
Definition term752 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_neg (real_of_num (Nat.add (Nat.add x1 x0) x1))) = (real_of_num y0).
Definition term720 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_neg (real_of_num (Nat.add x0 (Nat.add x0 x1)))) = (real_of_num y0).
Definition term742 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y1))) y0.
Definition term710 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_neg (real_of_num y1))) y0.
Definition term366 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y1))) y0.
Definition term335 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y1))) y0.
Definition term302 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_neg (real_of_num y1))) y0.
Definition term271 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_neg (real_of_num y1))) y0.
Definition term238 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num y1))) y0.
Definition term205 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y1))) y0.
Definition term105 (x0 : int) (x1 : int) := fun y0 : nat => (fun y1 : nat => (real_add (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y1))) y0.
Definition term523 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term605 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term145 (x0 : nat) (x1 : nat) := True \/ (exists y0 : nat, (real_of_num (Nat.add x0 x1)) = (real_neg (real_of_num y0))).
Definition term254 (x0 : nat) (x1 : nat) := @eq real (real_add (real_add (real_of_num x1) (real_of_num x0)) (real_neg (real_of_num x1))).
Definition term403 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term569 (x0 : nat) (x1 : nat) := real_sub (real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) (real_of_num x1).
Definition term634 (x0 : nat) (x1 : nat) := ((real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) = (real_of_num x1)) \/ ((real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) = (real_neg (real_of_num x1))).
Definition term691 (x0 : nat) (x1 : nat) := (~ (((real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) = (real_of_num x1)) \/ ((real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) = (real_neg (real_of_num x1))))) -> False.
Definition term661 (x0 : nat) (x1 : nat) := (~ (((real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) = (real_of_num x1)) \/ ((real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) = (real_neg (real_of_num x1))))) -> False.
Definition term632 (x0 : nat) (x1 : nat) := (~ (((real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) = (real_of_num x1)) \/ ((real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) = (real_neg (real_of_num x1))))) -> False.
Definition term557 (x0 : nat) (x1 : nat) := (~ (((real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num x1)) \/ ((real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_neg (real_of_num x1))))) -> False.
Definition term317 (x0 : nat) (x1 : nat) := @eq real (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)).
Definition term129 (x0 : nat) (x1 : nat) := @eq real (real_add (real_neg (real_of_num x0)) (real_of_num x1)).
Definition term672 (x0 : nat) (x1 : nat) := real_sub (real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) (real_of_num x1).
Definition term25 (x0 : nat) (x1 : nat) := real_add (real_of_num x0) (real_of_num x1).
Definition term756 (x0 : nat) (x1 : nat) := exists y0 : nat, (Nat.add (Nat.add x1 x0) x1) = y0.
Definition term114 (x0 : nat) (x1 : nat) := exists y0 : nat, (Nat.add x0 x1) = y0.
Definition term717 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.add x0 (Nat.add x0 x1))).
Definition term231 (x0 : nat) (x1 : nat) := real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1)).
Definition term383 (x0 : nat) (x1 : nat) := fun y0 : nat => ((real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ ((real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))).
Definition term376 (x0 : nat) (x1 : nat) := fun y0 : nat => ((real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ ((real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))).
Definition term352 (x0 : nat) (x1 : nat) := fun y0 : nat => ((real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num y0)) \/ ((real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_neg (real_of_num y0))).
Definition term345 (x0 : nat) (x1 : nat) := fun y0 : nat => ((real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y0)) \/ ((real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y0))).
Definition term321 (x0 : nat) (x1 : nat) := fun y0 : nat => ((real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_of_num x1)) = (real_of_num y0)) \/ ((real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_of_num x1)) = (real_neg (real_of_num y0))).
Definition term312 (x0 : nat) (x1 : nat) := fun y0 : nat => ((real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_of_num y0)) \/ ((real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_neg (real_of_num y0))).
Definition term288 (x0 : nat) (x1 : nat) := fun y0 : nat => ((real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) = (real_of_num y0)) \/ ((real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) = (real_neg (real_of_num y0))).
Definition term281 (x0 : nat) (x1 : nat) := fun y0 : nat => ((real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_of_num y0)) \/ ((real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_neg (real_of_num y0))).
Definition term257 (x0 : nat) (x1 : nat) := fun y0 : nat => ((real_add (real_add (real_of_num x1) (real_of_num x0)) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ ((real_add (real_add (real_of_num x1) (real_of_num x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))).
Definition term248 (x0 : nat) (x1 : nat) := fun y0 : nat => ((real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ ((real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))).
Definition term224 (x0 : nat) (x1 : nat) := fun y0 : nat => ((real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num y0)) \/ ((real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_neg (real_of_num y0))).
Definition term215 (x0 : nat) (x1 : nat) := fun y0 : nat => ((real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y0)) \/ ((real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y0))).
Definition term97 (x0 : int) (x1 : int) := fun y0 : nat => ((real_add (real_of_int x0) (real_of_int x1)) = (real_of_num y0)) \/ ((real_add (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y0))).
Definition term253 (x0 : nat) (x1 : nat) := @eq real (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))).
Definition term20 (x0 : nat) := forall y0 : nat, ((real_of_num x0) = (real_of_num y0)) = (x0 = y0).
Definition term567 (x0 : nat) (x1 : nat) := real_sub (real_add (real_add (real_of_num x1) (real_of_num x0)) (real_neg (real_of_num x1))).
Definition term748 (x0 : nat) (x1 : nat) := real_of_num (Nat.add (Nat.add x1 x0) x1).
Definition term587 := real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term520 := real_neg (real_of_num (NUMERAL 0)).
Definition term57 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) \/ (Peano.le y0 x0)) x1.
Definition term590 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term589 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term449 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term447 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term413 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term407 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term52 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1)).
Definition term435 := real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term471 (x0 : nat) := real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0).
Definition term389 (x0 : nat) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0).
Definition term730 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_of_num y0)) x2.
Definition term698 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num y0)) x2.
Definition term358 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_of_num y0)) x2.
Definition term327 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y0)) x2.
Definition term294 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_of_num y0)) x2.
Definition term263 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_of_num y0)) x2.
Definition term230 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_of_num y0)) x2.
Definition term197 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y0)) x2.
Definition term89 (x0 : int) (x1 : int) (x2 : nat) := (fun y0 : nat => (real_add (real_of_int x0) (real_of_int x1)) = (real_of_num y0)) x2.
Definition term144 (x0 : nat) := exists y0 : nat, x0 = y0.
Definition term610 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term190 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (real_add (real_neg (real_of_num y0)) (real_neg (real_of_num x0))) = (real_of_num y1)) \/ (exists y1 : nat, (real_add (real_neg (real_of_num y0)) (real_neg (real_of_num x0))) = (real_neg (real_of_num y1)))) (Nat.add x0 x1).
Definition term184 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num y0))) = (real_of_num y1)) \/ (exists y1 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num y0))) = (real_neg (real_of_num y1)))) (Nat.add x0 x1).
Definition term179 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (real_add (real_neg (real_of_num y0)) (real_of_num x0)) = (real_of_num y1)) \/ (exists y1 : nat, (real_add (real_neg (real_of_num y0)) (real_of_num x0)) = (real_neg (real_of_num y1)))) (Nat.add x0 x1).
Definition term173 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num y0)) = (real_of_num y1)) \/ (exists y1 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num y0)) = (real_neg (real_of_num y1)))) (Nat.add x0 x1).
Definition term168 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (real_add (real_of_num y0) (real_neg (real_of_num x0))) = (real_of_num y1)) \/ (exists y1 : nat, (real_add (real_of_num y0) (real_neg (real_of_num x0))) = (real_neg (real_of_num y1)))) (Nat.add x0 x1).
Definition term162 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (real_add (real_of_num x0) (real_neg (real_of_num y0))) = (real_of_num y1)) \/ (exists y1 : nat, (real_add (real_of_num x0) (real_neg (real_of_num y0))) = (real_neg (real_of_num y1)))) (Nat.add x0 x1).
Definition term5 (a0 : Type') := fun y0 : a0 => exists y1 : a0, y0 = y1.
Definition term64 (x0 : int) := forall y0 : int, (int_add x0 y0) = (int_of_real (real_add (real_of_int x0) (real_of_int y0))).
Definition term192 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => (exists y1 : nat, (real_add (real_neg (real_of_num y0)) (real_neg (real_of_num x0))) = (real_of_num y1)) \/ (exists y1 : nat, (real_add (real_neg (real_of_num y0)) (real_neg (real_of_num x0))) = (real_neg (real_of_num y1)))) x1).
Definition term186 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => (exists y1 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num y0))) = (real_of_num y1)) \/ (exists y1 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num y0))) = (real_neg (real_of_num y1)))) x1).
Definition term181 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => (exists y1 : nat, (real_add (real_neg (real_of_num y0)) (real_of_num x0)) = (real_of_num y1)) \/ (exists y1 : nat, (real_add (real_neg (real_of_num y0)) (real_of_num x0)) = (real_neg (real_of_num y1)))) x1).
Definition term175 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => (exists y1 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num y0)) = (real_of_num y1)) \/ (exists y1 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num y0)) = (real_neg (real_of_num y1)))) x1).
Definition term170 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => (exists y1 : nat, (real_add (real_of_num y0) (real_neg (real_of_num x0))) = (real_of_num y1)) \/ (exists y1 : nat, (real_add (real_of_num y0) (real_neg (real_of_num x0))) = (real_neg (real_of_num y1)))) x1).
Definition term164 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => (exists y1 : nat, (real_add (real_of_num x0) (real_neg (real_of_num y0))) = (real_of_num y1)) \/ (exists y1 : nat, (real_add (real_of_num x0) (real_neg (real_of_num y0))) = (real_neg (real_of_num y1)))) x1).
Definition term747 (x0 : nat) (x1 : nat) := real_add (real_of_num (Nat.add x1 x0)) (real_of_num x1).
Definition term146 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term198 (x0 : nat) (x1 : nat) := real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1))).
Definition term674 (x0 : nat) (x1 : nat) := @eq real (real_neg (real_sub (real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) (real_of_num x1))).
Definition term644 (x0 : nat) (x1 : nat) := @eq real (real_neg (real_sub (real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) (real_of_num x1))).
Definition term572 (x0 : nat) (x1 : nat) := @eq real (real_neg (real_sub (real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) (real_of_num x1))).
Definition term491 (x0 : nat) (x1 : nat) := @eq real (real_neg (real_sub (real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) (real_of_num x1))).
Definition term728 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_of_num y0).
Definition term356 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_of_num y0).
Definition term325 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y0).
Definition term261 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_of_num y0).
Definition term228 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_of_num y0).
Definition term195 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y0).
Definition term138 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_of_num y0).
Definition term121 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_add (real_of_num x0) (real_neg (real_of_num x1))) = (real_of_num y0).
Definition term48 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => ((exists y1 : a0, x0 y1) \/ (exists y1 : a0, y0 y1)) = (exists y1 : a0, (x0 y1) \/ (y0 y1))) x1.
Definition term464 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL (BIT1 0)))).
Definition term425 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term749 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.add (Nat.add x1 x0) x1)).
Definition term68 (x0 : int) (x1 : int) := real_of_int (int_of_real (real_add (real_of_int x0) (real_of_int x1))).
Definition term639 (x0 : nat) (x1 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1)) (real_add (real_of_num x0) (real_of_num x1)).
Definition term62 (x0 : real) := real_of_int (int_of_real x0).
Definition term469 := real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term402 := real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term700 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_neg (real_of_num y0))) x2.
Definition term688 (x0 : nat) (x1 : nat) := real_gt (real_sub (real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num (NUMERAL 0)).
Definition term658 (x0 : nat) (x1 : nat) := real_gt (real_sub (real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) (real_neg (real_of_num x1))) (real_of_num (NUMERAL 0)).
Definition term615 (x0 : nat) (x1 : nat) := real_gt (real_sub (real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) (real_of_num (NUMERAL 0)).
Definition term533 (x0 : nat) (x1 : nat) := real_gt (real_sub (real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) (real_neg (real_of_num x1))) (real_of_num (NUMERAL 0)).
Definition term219 (x0 : nat) (x1 : nat) := real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))).
Definition term382 (x0 : nat) (x1 : nat) (x2 : nat) := ((real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_of_num x2)) \/ ((real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num x2))).
Definition term374 (x0 : nat) (x1 : nat) (x2 : nat) := ((real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_of_num x2)) \/ ((real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num x2))).
Definition term343 (x0 : nat) (x1 : nat) (x2 : nat) := ((real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num x2)) \/ ((real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num x2))).
Definition term279 (x0 : nat) (x1 : nat) (x2 : nat) := ((real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_of_num x2)) \/ ((real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_neg (real_of_num x2))).
Definition term256 (x0 : nat) (x1 : nat) (x2 : nat) := ((real_add (real_add (real_of_num x1) (real_of_num x0)) (real_neg (real_of_num x1))) = (real_of_num x2)) \/ ((real_add (real_add (real_of_num x1) (real_of_num x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num x2))).
Definition term246 (x0 : nat) (x1 : nat) (x2 : nat) := ((real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_of_num x2)) \/ ((real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num x2))).
Definition term213 (x0 : nat) (x1 : nat) (x2 : nat) := ((real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num x2)) \/ ((real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num x2))).
Definition term295 (x0 : nat) (x1 : nat) := real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1).
Definition term7 (a0 : Type') := forall y0 : a0, exists y1 : a0, y0 = y1.
Definition term6 (a0 : Type') := forall y0 : a0, exists y1 : a0, y1 = y0.
Definition term159 (x0 : nat) (x1 : nat) := (exists y0 : nat, x0 = (Nat.add x1 y0)) -> (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))).
Definition term157 (x0 : nat) (x1 : nat) := (exists y0 : nat, x1 = (Nat.add x0 y0)) -> (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))).
Definition term155 (x0 : nat) (x1 : nat) := (exists y0 : nat, x0 = (Nat.add x1 y0)) -> (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num x1)) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num x1)) = (real_neg (real_of_num y0))).
Definition term153 (x0 : nat) (x1 : nat) := (exists y0 : nat, x1 = (Nat.add x0 y0)) -> (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num x1)) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num x1)) = (real_neg (real_of_num y0))).
Definition term151 (x0 : nat) (x1 : nat) := (exists y0 : nat, x0 = (Nat.add x1 y0)) -> (exists y0 : nat, (real_add (real_of_num x0) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_of_num x0) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))).
Definition term149 (x0 : nat) (x1 : nat) := (exists y0 : nat, x1 = (Nat.add x0 y0)) -> (exists y0 : nat, (real_add (real_of_num x0) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_of_num x0) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))).
Definition term665 (x0 : nat) (x1 : nat) := (~ ((real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) = (real_of_num x1))) /\ (~ ((real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) = (real_neg (real_of_num x1)))).
Definition term636 (x0 : nat) (x1 : nat) := (~ ((real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) = (real_of_num x1))) /\ (~ ((real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) = (real_neg (real_of_num x1)))).
Definition term561 (x0 : nat) (x1 : nat) := (~ ((real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) = (real_of_num x1))) /\ (~ ((real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) = (real_neg (real_of_num x1)))).
Definition term386 (x0 : nat) (x1 : nat) := (~ ((real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num x1))) /\ (~ ((real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_neg (real_of_num x1)))).
Definition term411 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term112 (x0 : nat) (x1 : nat) := @eq real (real_of_num (Nat.add x0 x1)).
Definition term264 (x0 : nat) (x1 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1)).
Definition term524 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term17 := forall y0 : real, forall y1 : real, (real_add (real_neg y0) (real_neg y1)) = (real_neg (real_add y0 y1)).
Definition term16 := forall y0 : real, forall y1 : real, (real_neg (real_add y0 y1)) = (real_add (real_neg y0) (real_neg y1)).
Definition term565 (x0 : nat) (x1 : nat) := real_add (real_of_num x0) (real_add (real_of_num x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1))).
Definition term18 (a0 : Type') (x0 : a0) := (fun y0 : a0 => exists y1 : a0, y0 = y1) x0.
Definition term147 (x0 : nat) (x1 : nat) := imp (exists y0 : nat, x0 = (Nat.add x1 y0)).
Definition term349 (x0 : nat) (x1 : nat) := @eq real (real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))).
Definition term737 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_of_num y1)) y0.
Definition term705 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num y1)) y0.
Definition term360 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_of_num y1)) y0.
Definition term329 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y1)) y0.
Definition term296 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_of_num y1)) y0.
Definition term265 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_of_num y1)) y0.
Definition term232 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_of_num y1)) y0.
Definition term199 (x0 : nat) (x1 : nat) := fun y0 : nat => (fun y1 : nat => (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y1)) y0.
Definition term100 (x0 : int) (x1 : int) := fun y0 : nat => (fun y1 : nat => (real_add (real_of_int x0) (real_of_int x1)) = (real_of_num y1)) y0.
Definition term510 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term478 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term522 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term119 (x0 : nat) (x1 : nat) := real_add (real_of_num x0) (real_neg (real_of_num x1)).
Definition term716 (x0 : nat) (x1 : nat) := real_of_num (Nat.add x0 (Nat.add x0 x1)).
Definition term591 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term450 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term414 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> ((real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))) = (real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))))) -> (real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) = (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term718 (x0 : nat) (x1 : nat) := @eq real (real_neg (real_of_num (Nat.add x0 (Nat.add x0 x1)))).
Definition term489 := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term588 := real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term406 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term285 (x0 : nat) (x1 : nat) := @eq real (real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))).
Definition term482 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0)))).
Definition term116 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_of_num (Nat.add x0 x1)) = (real_neg (real_of_num y0)).
Definition term59 (x0 : int) := (fun y0 : int => exists y1 : nat, ((real_of_int y0) = (real_of_num y1)) \/ ((real_of_int y0) = (real_neg (real_of_num y1)))) x0.
Definition term732 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))) x2.
Definition term365 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))) x2.
Definition term334 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y0))) x2.
Definition term270 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_neg (real_of_num y0))) x2.
Definition term237 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))) x2.
Definition term204 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y0))) x2.
Definition term77 (x0 : int) := forall y0 : int, (real_of_int (int_add x0 y0)) = (real_add (real_of_int x0) (real_of_int y0)).
Definition term456 := Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term759 (x0 : int) := fun y0 : nat => ((real_of_int x0) = (real_of_num y0)) \/ ((real_of_int x0) = (real_neg (real_of_num y0))).
Definition term120 (x0 : nat) (x1 : nat) := @eq real (real_add (real_of_num x0) (real_neg (real_of_num x1))).
Definition term438 (x0 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term67 (x0 : int) (x1 : int) := real_of_int (int_add x0 x1).
Definition term33 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0 -> Prop, (exists y1 : a0, (x0 y1) \/ (y0 y1)) = ((exists y1 : a0, x0 y1) \/ (exists y1 : a0, y0 y1)).
Definition term24 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_add (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.add x0 y0))) x1.
Definition term113 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add x0 x1) = y0.
Definition term117 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_of_num (Nat.add x0 x1)) = (real_neg (real_of_num y0)).
Definition term315 (x0 : nat) (x1 : nat) := real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))).
Definition term540 (x0 : nat) := (((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL 0)))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) \/ (((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL 0)))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term578 (x0 : nat) (x1 : nat) := ~ ((real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) = (real_neg (real_of_num x1))).
Definition term468 := real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term56 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) \/ (Peano.le y0 x0).
Definition term548 := real_lt (real_of_num (NUMERAL 0)).
Definition term220 (x0 : nat) (x1 : nat) := @eq real (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))).
Definition term570 (x0 : nat) := real_sub (real_of_num x0) (real_of_num x0).
Definition term75 (x0 : int) := fun y0 : int => (real_of_int (int_add x0 y0)) = (real_add (real_of_int x0) (real_of_int y0)).
Definition term221 (x0 : nat) (x1 : nat) := @eq real (real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))).
Definition term508 (x0 : nat) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)).
Definition term474 (x0 : nat) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0)).
Definition term736 (x0 : nat) (x1 : nat) := @eq Prop (exists y0 : nat, ((real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ ((real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0)))).
Definition term735 (x0 : nat) (x1 : nat) := @eq Prop (exists y0 : nat, ((fun y1 : nat => (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_of_num y1)) y0) \/ ((fun y1 : nat => (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y1))) y0)).
Definition term704 (x0 : nat) (x1 : nat) := @eq Prop (exists y0 : nat, ((real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num y0)) \/ ((real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_neg (real_of_num y0)))).
Definition term703 (x0 : nat) (x1 : nat) := @eq Prop (exists y0 : nat, ((fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num y1)) y0) \/ ((fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_neg (real_of_num y1))) y0)).
Definition term99 (x0 : int) (x1 : int) := @eq Prop (exists y0 : nat, ((real_add (real_of_int x0) (real_of_int x1)) = (real_of_num y0)) \/ ((real_add (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y0)))).
Definition term98 (x0 : int) (x1 : int) := @eq Prop (exists y0 : nat, ((fun y1 : nat => (real_add (real_of_int x0) (real_of_int x1)) = (real_of_num y1)) y0) \/ ((fun y1 : nat => (real_add (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y1))) y0)).
Definition term581 (x0 : nat) := real_sub (real_of_num x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)).
Definition term384 (x0 : nat) (x1 : nat) := exists y0 : nat, ((real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ ((real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))).
Definition term377 (x0 : nat) (x1 : nat) := exists y0 : nat, ((real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ ((real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))).
Definition term353 (x0 : nat) (x1 : nat) := exists y0 : nat, ((real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num y0)) \/ ((real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_neg (real_of_num y0))).
Definition term346 (x0 : nat) (x1 : nat) := exists y0 : nat, ((real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y0)) \/ ((real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y0))).
Definition term322 (x0 : nat) (x1 : nat) := exists y0 : nat, ((real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_of_num x1)) = (real_of_num y0)) \/ ((real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_of_num x1)) = (real_neg (real_of_num y0))).
Definition term313 (x0 : nat) (x1 : nat) := exists y0 : nat, ((real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_of_num y0)) \/ ((real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_neg (real_of_num y0))).
Definition term289 (x0 : nat) (x1 : nat) := exists y0 : nat, ((real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) = (real_of_num y0)) \/ ((real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) = (real_neg (real_of_num y0))).
Definition term282 (x0 : nat) (x1 : nat) := exists y0 : nat, ((real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_of_num y0)) \/ ((real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_neg (real_of_num y0))).
Definition term258 (x0 : nat) (x1 : nat) := exists y0 : nat, ((real_add (real_add (real_of_num x1) (real_of_num x0)) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ ((real_add (real_add (real_of_num x1) (real_of_num x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))).
Definition term249 (x0 : nat) (x1 : nat) := exists y0 : nat, ((real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ ((real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))).
Definition term225 (x0 : nat) (x1 : nat) := exists y0 : nat, ((real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num y0)) \/ ((real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_neg (real_of_num y0))).
Definition term216 (x0 : nat) (x1 : nat) := exists y0 : nat, ((real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y0)) \/ ((real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y0))).
Definition term74 (x0 : int) (x1 : int) := exists y0 : nat, ((real_add (real_of_int x0) (real_of_int x1)) = (real_of_num y0)) \/ ((real_add (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y0))).
Definition term60 (x0 : int) := exists y0 : nat, ((real_of_int x0) = (real_of_num y0)) \/ ((real_of_int x0) = (real_neg (real_of_num y0))).
Definition term109 (x0 : int) := real_add (real_of_int x0).
Definition term379 (x0 : nat) (x1 : nat) := @eq real (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))).
Definition term666 (x0 : nat) (x1 : nat) := ~ ((real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) = (real_of_num x1)).
Definition term614 (x0 : nat) (x1 : nat) := real_gt (real_sub (real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))).
Definition term604 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term473 (x0 : nat) := real_neg (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0)).
Definition term292 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_of_num y0).
Definition term130 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_add (real_neg (real_of_num x0)) (real_of_num x1)) = (real_of_num y0).
Definition term87 (x0 : int) (x1 : int) := fun y0 : nat => (real_add (real_of_int x0) (real_of_int x1)) = (real_of_num y0).
Definition term622 (x0 : nat) := (((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL 0)))) \/ (((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0)) (real_of_num (NUMERAL 0)))).
Definition term671 (x0 : nat) (x1 : nat) := real_sub (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_of_num x1)).
Definition term441 (x0 : nat) (x1 : nat) := real_sub (real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) (real_of_num x1).
Definition term564 (x0 : nat) (x1 : nat) := real_add (real_add (real_of_num x0) (real_of_num x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1)).
Definition term453 := real_neg (real_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)))).
Definition term50 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_of_num (Nat.add x0 y0)) = (real_add (real_of_num x0) (real_of_num y0))) x1.
Definition term493 (x0 : nat) := real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)).
Definition term14 := fun y0 : real => forall y1 : real, (real_neg (real_add y0 y1)) = (real_add (real_neg y0) (real_neg y1)).
Definition term744 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0)).
Definition term712 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_neg (real_of_num y0)).
Definition term368 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0)).
Definition term337 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y0)).
Definition term304 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_neg (real_of_num y0)).
Definition term273 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_neg (real_of_num y0)).
Definition term240 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0)).
Definition term207 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y0)).
Definition term142 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0)).
Definition term134 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num x1)) = (real_neg (real_of_num y0)).
Definition term125 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_add (real_of_num x0) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0)).
Definition term107 (x0 : int) (x1 : int) := exists y0 : nat, (real_add (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y0)).
Definition term432 := real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term499 (x0 : nat) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term495 (x0 : nat) := real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term571 (x0 : nat) (x1 : nat) := real_neg (real_sub (real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) (real_of_num x1)).
Definition term727 (x0 : nat) (x1 : nat) := (exists y0 : nat, (fun y1 : nat => (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_of_num y1)) y0) \/ (exists y0 : nat, (fun y1 : nat => (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y1))) y0).
Definition term695 (x0 : nat) (x1 : nat) := (exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num y1)) y0) \/ (exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_neg (real_of_num y1))) y0).
Definition term354 (x0 : nat) (x1 : nat) := (exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_of_num y1)) y0) \/ (exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y1))) y0).
Definition term323 (x0 : nat) (x1 : nat) := (exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y1)) y0) \/ (exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y1))) y0).
Definition term290 (x0 : nat) (x1 : nat) := (exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_of_num y1)) y0) \/ (exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_neg (real_of_num y1))) y0).
Definition term259 (x0 : nat) (x1 : nat) := (exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_of_num y1)) y0) \/ (exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_neg (real_of_num y1))) y0).
Definition term226 (x0 : nat) (x1 : nat) := (exists y0 : nat, (fun y1 : nat => (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_of_num y1)) y0) \/ (exists y0 : nat, (fun y1 : nat => (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num y1))) y0).
Definition term193 (x0 : nat) (x1 : nat) := (exists y0 : nat, (fun y1 : nat => (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y1)) y0) \/ (exists y0 : nat, (fun y1 : nat => (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y1))) y0).
Definition term86 (x0 : int) (x1 : int) := (exists y0 : nat, (fun y1 : nat => (real_add (real_of_int x0) (real_of_int x1)) = (real_of_num y1)) y0) \/ (exists y0 : nat, (fun y1 : nat => (real_add (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y1))) y0).
Definition term680 (x0 : nat) (x1 : nat) := ~ ((real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) = (real_neg (real_of_num x1))).
Definition term690 (x0 : nat) (x1 : nat) := and (~ ((real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) = (real_of_num x1))).
Definition term660 (x0 : nat) (x1 : nat) := and (~ ((real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) = (real_of_num x1))).
Definition term619 (x0 : nat) (x1 : nat) := and (~ ((real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) = (real_of_num x1))).
Definition term537 (x0 : nat) (x1 : nat) := and (~ ((real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num x1))).
Definition term428 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term421 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term512 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term480 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term536 := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term618 (x0 : nat) := (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0)) (real_of_num (NUMERAL 0))).
Definition term502 (x0 : nat) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL 0))).
Definition term509 (x0 : nat) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num x0).
Definition term475 (x0 : nat) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))))) (real_of_num x0).
Definition term71 (x0 : int) (x1 : int) := real_add (real_of_int x0) (real_of_int x1).
Definition term404 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term681 (x0 : nat) (x1 : nat) := (real_gt (real_sub (real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) (real_neg (real_of_num x1)))) (real_of_num (NUMERAL 0))).
Definition term667 (x0 : nat) (x1 : nat) := (real_gt (real_sub (real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) (real_of_num x1)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) (real_of_num x1))) (real_of_num (NUMERAL 0))).
Definition term651 (x0 : nat) (x1 : nat) := (real_gt (real_sub (real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) (real_neg (real_of_num x1))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) (real_neg (real_of_num x1)))) (real_of_num (NUMERAL 0))).
Definition term638 (x0 : nat) (x1 : nat) := (real_gt (real_sub (real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) (real_of_num x1)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) (real_of_num x1))) (real_of_num (NUMERAL 0))).
Definition term579 (x0 : nat) (x1 : nat) := (real_gt (real_sub (real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1)))) (real_of_num (NUMERAL 0))).
Definition term563 (x0 : nat) (x1 : nat) := (real_gt (real_sub (real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) (real_of_num x1)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) (real_of_num x1))) (real_of_num (NUMERAL 0))).
Definition term504 (x0 : nat) (x1 : nat) := (real_gt (real_sub (real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) (real_neg (real_of_num x1))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) (real_neg (real_of_num x1)))) (real_of_num (NUMERAL 0))).
Definition term388 (x0 : nat) (x1 : nat) := (real_gt (real_sub (real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) (real_of_num x1)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) (real_of_num x1))) (real_of_num (NUMERAL 0))).
Definition term350 (x0 : nat) (x1 : nat) (x2 : nat) := or ((real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num x2)).
Definition term286 (x0 : nat) (x1 : nat) (x2 : nat) := or ((real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) = (real_of_num x2)).
Definition term222 (x0 : nat) (x1 : nat) (x2 : nat) := or ((real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num x2)).
Definition term555 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term521 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term687 (x0 : nat) (x1 : nat) := real_gt (real_sub (real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) (real_neg (real_of_num x1))).
Definition term641 (x0 : nat) (x1 : nat) := real_sub (real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))).
Definition term600 (x0 : nat) (x1 : nat) := real_neg (real_sub (real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))).
Definition term739 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_of_num y0).
Definition term707 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num y0).
Definition term362 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_of_num y0).
Definition term331 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y0).
Definition term298 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_of_num y0).
Definition term267 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_of_num y0).
Definition term234 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_of_num y0).
Definition term201 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y0).
Definition term139 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_of_num y0).
Definition term131 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num x1)) = (real_of_num y0).
Definition term122 (x0 : nat) (x1 : nat) := exists y0 : nat, (real_add (real_of_num x0) (real_neg (real_of_num x1))) = (real_of_num y0).
Definition term102 (x0 : int) (x1 : int) := exists y0 : nat, (real_add (real_of_int x0) (real_of_int x1)) = (real_of_num y0).
Definition term316 (x0 : nat) (x1 : nat) := real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_of_num x1).
Definition term583 (x0 : nat) := real_add (real_of_num x0) (real_of_num x0).
Definition term608 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term757 (x0 : nat) (x1 : nat) := (exists y0 : nat, (real_neg (real_of_num (Nat.add (Nat.add x1 x0) x1))) = (real_of_num y0)) \/ True.
Definition term725 (x0 : nat) (x1 : nat) := (exists y0 : nat, (real_neg (real_of_num (Nat.add x0 (Nat.add x0 x1)))) = (real_of_num y0)) \/ True.
Definition term69 (x0 : int) (x1 : int) := @eq real (real_of_int (int_add x0 x1)).
Definition term54 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.add x1 y0).
Definition term754 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x1 x0) x1.
Definition term136 (x0 : nat) (x1 : nat) := real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term518 (x0 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_of_num x0).
Definition term410 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))).
Definition term466 := Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL (BIT1 0)).
Definition term580 (x0 : nat) (x1 : nat) := real_sub (real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1)).
Definition term562 (x0 : nat) (x1 : nat) := ~ ((real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) = (real_of_num x1)).
Definition term531 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term550 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term43 := forall y0 : nat, forall y1 : nat, (real_of_num (Nat.add y0 y1)) = (real_add (real_of_num y0) (real_of_num y1)).
Definition term42 := forall y0 : nat, forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1)).
Definition term448 := real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term676 (x0 : nat) (x1 : nat) := real_gt (real_neg (real_sub (real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) (real_of_num x1))) (real_of_num (NUMERAL 0)).
Definition term646 (x0 : nat) (x1 : nat) := real_gt (real_neg (real_sub (real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) (real_of_num x1))) (real_of_num (NUMERAL 0)).
Definition term574 (x0 : nat) (x1 : nat) := real_gt (real_neg (real_sub (real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) (real_of_num x1))) (real_of_num (NUMERAL 0)).
Definition term494 (x0 : nat) (x1 : nat) := real_gt (real_neg (real_sub (real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) (real_of_num x1))) (real_of_num (NUMERAL 0)).
Definition term45 (x0 : real) (x1 : real) := (fun y0 : real => (real_neg (real_add x0 y0)) = (real_add (real_neg x0) (real_neg y0))) x1.
Definition term422 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num x1).
Definition term137 (x0 : nat) (x1 : nat) := @eq real (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))).
Definition term80 := fun y0 : int => forall y1 : int, exists y2 : nat, ((real_add (real_of_int y0) (real_of_int y1)) = (real_of_num y2)) \/ ((real_add (real_of_int y0) (real_of_int y1)) = (real_neg (real_of_num y2))).
Definition term582 (x0 : nat) := real_add (real_of_num x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0))).
Definition term39 (x0 : nat) := forall y0 : nat, (real_of_num (Nat.add x0 y0)) = (real_add (real_of_num x0) (real_of_num y0)).
Definition term726 (x0 : nat) (x1 : nat) := exists y0 : nat, ((fun y1 : nat => (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_of_num y1)) y0) \/ ((fun y1 : nat => (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y1))) y0).
Definition term694 (x0 : nat) (x1 : nat) := exists y0 : nat, ((fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num y1)) y0) \/ ((fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_neg (real_of_num y1))) y0).
Definition term355 (x0 : nat) (x1 : nat) := exists y0 : nat, ((fun y1 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_of_num y1)) y0) \/ ((fun y1 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y1))) y0).
Definition term324 (x0 : nat) (x1 : nat) := exists y0 : nat, ((fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y1)) y0) \/ ((fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y1))) y0).
Definition term291 (x0 : nat) (x1 : nat) := exists y0 : nat, ((fun y1 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_of_num y1)) y0) \/ ((fun y1 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_neg (real_of_num y1))) y0).
Definition term260 (x0 : nat) (x1 : nat) := exists y0 : nat, ((fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_of_num y1)) y0) \/ ((fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_neg (real_of_num y1))) y0).
Definition term227 (x0 : nat) (x1 : nat) := exists y0 : nat, ((fun y1 : nat => (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_of_num y1)) y0) \/ ((fun y1 : nat => (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num y1))) y0).
Definition term194 (x0 : nat) (x1 : nat) := exists y0 : nat, ((fun y1 : nat => (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y1)) y0) \/ ((fun y1 : nat => (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y1))) y0).
Definition term85 (x0 : int) (x1 : int) := exists y0 : nat, ((fun y1 : nat => (real_add (real_of_int x0) (real_of_int x1)) = (real_of_num y1)) y0) \/ ((fun y1 : nat => (real_add (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y1))) y0).
Definition term13 (x0 : real) := forall y0 : real, (real_add (real_neg x0) (real_neg y0)) = (real_neg (real_add x0 y0)).
Definition term61 (x0 : int) (x1 : nat) := ((real_of_int x0) = (real_of_num x1)) \/ ((real_of_int x0) = (real_neg (real_of_num x1))).
Definition term515 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term488 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))))).
Definition term514 := real_div (real_of_num (NUMERAL (BIT1 0))).
Definition term597 := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term538 (x0 : nat) := and ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL 0)))).
Definition term693 (x0 : nat) (x1 : nat) := ((real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) = (real_of_num x1)) \/ ((real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) = (real_neg (real_of_num x1))).
Definition term250 (x0 : nat) (x1 : nat) := real_add (real_of_num (Nat.add x0 x1)).
Definition term609 := real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term692 (x0 : nat) (x1 : nat) := ((~ (((real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) = (real_of_num x1)) \/ ((real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) = (real_neg (real_of_num x1))))) -> False) -> ((real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) = (real_of_num x1)) \/ ((real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) = (real_neg (real_of_num x1))).
Definition term662 (x0 : nat) (x1 : nat) := ((~ (((real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) = (real_of_num x1)) \/ ((real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) = (real_neg (real_of_num x1))))) -> False) -> ((real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) = (real_of_num x1)) \/ ((real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) = (real_neg (real_of_num x1))).
Definition term633 (x0 : nat) (x1 : nat) := ((~ (((real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) = (real_of_num x1)) \/ ((real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) = (real_neg (real_of_num x1))))) -> False) -> ((real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) = (real_of_num x1)) \/ ((real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) = (real_neg (real_of_num x1))).
Definition term558 (x0 : nat) (x1 : nat) := ((~ (((real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num x1)) \/ ((real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_neg (real_of_num x1))))) -> False) -> ((real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num x1)) \/ ((real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_neg (real_of_num x1))).
Definition term626 (x0 : nat) := ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL 0)))).
Definition term624 (x0 : nat) := ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0)) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0)) (real_of_num (NUMERAL 0)))).
Definition term543 (x0 : nat) := or (((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL 0)))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term686 (x0 : nat) (x1 : nat) := real_gt (real_neg (real_sub (real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) (real_neg (real_of_num x1)))) (real_of_num (NUMERAL 0)).
Definition term656 (x0 : nat) (x1 : nat) := real_gt (real_neg (real_sub (real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) (real_neg (real_of_num x1)))) (real_of_num (NUMERAL 0)).
Definition term613 (x0 : nat) (x1 : nat) := real_gt (real_neg (real_sub (real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1)))) (real_of_num (NUMERAL 0)).
Definition term530 (x0 : nat) (x1 : nat) := real_gt (real_neg (real_sub (real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) (real_neg (real_of_num x1)))) (real_of_num (NUMERAL 0)).
Definition term470 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term82 := forall y0 : int, forall y1 : int, exists y2 : nat, ((real_add (real_of_int y0) (real_of_int y1)) = (real_of_num y2)) \/ ((real_add (real_of_int y0) (real_of_int y1)) = (real_neg (real_of_num y2))).
Definition term81 := forall y0 : int, forall y1 : int, (real_of_int (int_add y0 y1)) = (real_add (real_of_int y0) (real_of_int y1)).
Definition term44 (x0 : real) := (fun y0 : real => forall y1 : real, (real_neg (real_add y0 y1)) = (real_add (real_neg y0) (real_neg y1))) x0.
Definition term30 (x0 : real) := (fun y0 : real => forall y1 : real, (real_add (real_neg y0) (real_neg y1)) = (real_neg (real_add y0 y1))) x0.
Definition term27 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_neg y0) = (real_neg y1)) = (y0 = y1)) x0.
Definition term72 (x0 : int) (x1 : int) := integer (real_add (real_of_int x0) (real_of_int x1)).
Definition term418 := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term542 (x0 : nat) := ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term714 (x0 : nat) (x1 : nat) := real_neg (real_add (real_of_num x0) (real_of_num (Nat.add x0 x1))).
Definition term46 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, ((exists y2 : a0, y0 y2) \/ (exists y2 : a0, y1 y2)) = (exists y2 : a0, (y0 y2) \/ (y1 y2))) x0.
Definition term32 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : a0 -> Prop, (exists y2 : a0, (y0 y2) \/ (y1 y2)) = ((exists y2 : a0, y0 y2) \/ (exists y2 : a0, y1 y2))) x0.
Definition term465 := Nat.mul (BIT0 (BIT1 0)) (BIT1 0).
Definition term552 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term696 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num y0).
Definition term467 := real_of_num (Nat.mul (NUMERAL (BIT0 (BIT1 0))) (NUMERAL (BIT1 0))).
Definition term412 := S (Nat.add 0 0).
Definition term476 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term461 := real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))).
Definition term668 (x0 : nat) (x1 : nat) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1))).
Definition term189 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (real_add (real_neg (real_of_num y0)) (real_neg (real_of_num x0))) = (real_of_num y1)) \/ (exists y1 : nat, (real_add (real_neg (real_of_num y0)) (real_neg (real_of_num x0))) = (real_neg (real_of_num y1)))) x1.
Definition term183 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num y0))) = (real_of_num y1)) \/ (exists y1 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num y0))) = (real_neg (real_of_num y1)))) x1.
Definition term178 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (real_add (real_neg (real_of_num y0)) (real_of_num x0)) = (real_of_num y1)) \/ (exists y1 : nat, (real_add (real_neg (real_of_num y0)) (real_of_num x0)) = (real_neg (real_of_num y1)))) x1.
Definition term172 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num y0)) = (real_of_num y1)) \/ (exists y1 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num y0)) = (real_neg (real_of_num y1)))) x1.
Definition term167 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (real_add (real_of_num y0) (real_neg (real_of_num x0))) = (real_of_num y1)) \/ (exists y1 : nat, (real_add (real_of_num y0) (real_neg (real_of_num x0))) = (real_neg (real_of_num y1)))) x1.
Definition term161 (x0 : nat) (x1 : nat) := (fun y0 : nat => (exists y1 : nat, (real_add (real_of_num x0) (real_neg (real_of_num y0))) = (real_of_num y1)) \/ (exists y1 : nat, (real_add (real_of_num x0) (real_neg (real_of_num y0))) = (real_neg (real_of_num y1)))) x1.
Definition term396 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term11 (x0 : real) := fun y0 : real => (real_add (real_neg x0) (real_neg y0)) = (real_neg (real_add x0 y0)).
Definition term679 (x0 : nat) (x1 : nat) := or (real_gt (real_sub (real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) (real_of_num x1)) (real_of_num (NUMERAL 0))).
Definition term649 (x0 : nat) (x1 : nat) := or (real_gt (real_sub (real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) (real_of_num x1)) (real_of_num (NUMERAL 0))).
Definition term617 (x0 : nat) := or (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL 0))).
Definition term577 (x0 : nat) (x1 : nat) := or (real_gt (real_sub (real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) (real_of_num x1)) (real_of_num (NUMERAL 0))).
Definition term501 (x0 : nat) := or (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0)) (real_of_num (NUMERAL 0))).
Definition term500 (x0 : nat) (x1 : nat) := or (real_gt (real_sub (real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) (real_of_num x1)) (real_of_num (NUMERAL 0))).
Definition term459 := real_of_num (NUMERAL (BIT0 (BIT1 0))).
Definition term463 := real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term424 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term8 (x0 : real) (x1 : real) := real_neg (real_add x0 x1).
Definition term684 (x0 : nat) (x1 : nat) := @eq real (real_neg (real_sub (real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) (real_neg (real_of_num x1)))).
Definition term654 (x0 : nat) (x1 : nat) := @eq real (real_neg (real_sub (real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) (real_neg (real_of_num x1)))).
Definition term611 (x0 : nat) (x1 : nat) := @eq real (real_neg (real_sub (real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1)))).
Definition term527 (x0 : nat) (x1 : nat) := @eq real (real_neg (real_sub (real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) (real_neg (real_of_num x1)))).
Definition term443 (x0 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)).
Definition term156 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))).
Definition term152 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num x1)) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num x1)) = (real_neg (real_of_num y0))).
Definition term148 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) -> (exists y0 : nat, (real_add (real_of_num x0) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_of_num x0) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0))).
Definition term58 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) \/ (Peano.le x0 x1).
Definition term620 := and ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term750 (x0 : nat) (x1 : nat) := @eq real (real_neg (real_of_num (Nat.add (Nat.add x1 x0) x1))).
Definition term2 (a0 : Type') (x0 : a0) := exists y0 : a0, y0 = x0.
Definition term628 (x0 : nat) := or (((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL 0))))).
Definition term544 (x0 : nat) := or (((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))))).
Definition term652 (x0 : nat) (x1 : nat) := real_sub (real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) (real_neg (real_of_num x1)).
Definition term566 (x0 : nat) := real_add (real_of_num x0) (real_of_num (NUMERAL 0)).
Definition term4 (a0 : Type') := fun y0 : a0 => exists y1 : a0, y1 = y0.
Definition term743 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y1))) y0.
Definition term738 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_of_num y1)) y0.
Definition term711 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_neg (real_of_num y1))) y0.
Definition term706 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num y1)) y0.
Definition term367 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y1))) y0.
Definition term361 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_of_num y1)) y0.
Definition term336 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y1))) y0.
Definition term330 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y1)) y0.
Definition term303 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_neg (real_of_num y1))) y0.
Definition term297 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_of_num y1)) y0.
Definition term272 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_neg (real_of_num y1))) y0.
Definition term266 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_of_num y1)) y0.
Definition term239 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num y1))) y0.
Definition term233 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_of_num y1)) y0.
Definition term206 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y1))) y0.
Definition term200 (x0 : nat) (x1 : nat) := exists y0 : nat, (fun y1 : nat => (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y1)) y0.
Definition term106 (x0 : int) (x1 : int) := exists y0 : nat, (fun y1 : nat => (real_add (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y1))) y0.
Definition term101 (x0 : int) (x1 : int) := exists y0 : nat, (fun y1 : nat => (real_add (real_of_int x0) (real_of_int x1)) = (real_of_num y1)) y0.
Definition term430 := real_mul (real_of_num (NUMERAL 0)).
Definition term29 (x0 : real) (x1 : real) := (fun y0 : real => ((real_neg x0) = (real_neg y0)) = (x0 = y0)) x1.
Definition term586 := real_add (real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term664 (x0 : nat) (x1 : nat) := ~ (((real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) = (real_of_num x1)) \/ ((real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) = (real_neg (real_of_num x1)))).
Definition term635 (x0 : nat) (x1 : nat) := ~ (((real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) = (real_of_num x1)) \/ ((real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) = (real_neg (real_of_num x1)))).
Definition term560 (x0 : nat) (x1 : nat) := ~ (((real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) = (real_of_num x1)) \/ ((real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) = (real_neg (real_of_num x1)))).
Definition term385 (x0 : nat) (x1 : nat) := ~ (((real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num x1)) \/ ((real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_neg (real_of_num x1)))).
Definition term751 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_neg (real_of_num (Nat.add (Nat.add x1 x0) x1))) = (real_of_num y0).
Definition term719 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_neg (real_of_num (Nat.add x0 (Nat.add x0 x1)))) = (real_of_num y0).
Definition term547 := real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term0 (a0 : Type') (x0 : a0) := fun y0 : a0 => y0 = x0.
Definition term66 (x0 : int) (x1 : int) := int_of_real (real_add (real_of_int x0) (real_of_int x1)).
Definition term457 := NUMERAL (BIT0 (BIT1 0)).
Definition term511 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term479 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term647 (x0 : nat) (x1 : nat) := real_gt (real_sub (real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) (real_of_num x1)).
Definition term496 (x0 : nat) (x1 : nat) := real_gt (real_sub (real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) (real_of_num x1)).
Definition term513 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term485 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0)))))).
Definition term440 (x0 : nat) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)).
Definition term416 (x0 : nat) (x1 : nat) := real_mul (real_of_num x0) (real_of_num x1).
Definition term444 (x0 : nat) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_of_num x0).
Definition term516 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term188 (x0 : nat) := fun y0 : nat => (exists y1 : nat, (real_add (real_neg (real_of_num y0)) (real_neg (real_of_num x0))) = (real_of_num y1)) \/ (exists y1 : nat, (real_add (real_neg (real_of_num y0)) (real_neg (real_of_num x0))) = (real_neg (real_of_num y1))).
Definition term182 (x0 : nat) := fun y0 : nat => (exists y1 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num y0))) = (real_of_num y1)) \/ (exists y1 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num y0))) = (real_neg (real_of_num y1))).
Definition term177 (x0 : nat) := fun y0 : nat => (exists y1 : nat, (real_add (real_neg (real_of_num y0)) (real_of_num x0)) = (real_of_num y1)) \/ (exists y1 : nat, (real_add (real_neg (real_of_num y0)) (real_of_num x0)) = (real_neg (real_of_num y1))).
Definition term171 (x0 : nat) := fun y0 : nat => (exists y1 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num y0)) = (real_of_num y1)) \/ (exists y1 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num y0)) = (real_neg (real_of_num y1))).
Definition term166 (x0 : nat) := fun y0 : nat => (exists y1 : nat, (real_add (real_of_num y0) (real_neg (real_of_num x0))) = (real_of_num y1)) \/ (exists y1 : nat, (real_add (real_of_num y0) (real_neg (real_of_num x0))) = (real_neg (real_of_num y1))).
Definition term160 (x0 : nat) := fun y0 : nat => (exists y1 : nat, (real_add (real_of_num x0) (real_neg (real_of_num y0))) = (real_of_num y1)) \/ (exists y1 : nat, (real_add (real_of_num x0) (real_neg (real_of_num y0))) = (real_neg (real_of_num y1))).
Definition term434 := real_mul (real_of_num (NUMERAL 0)) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term320 (x0 : nat) (x1 : nat) (x2 : nat) := ((real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_of_num x1)) = (real_of_num x2)) \/ ((real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_of_num x1)) = (real_neg (real_of_num x2))).
Definition term310 (x0 : nat) (x1 : nat) (x2 : nat) := ((real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_of_num x2)) \/ ((real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_neg (real_of_num x2))).
Definition term95 (x0 : int) (x1 : int) (x2 : nat) := ((real_add (real_of_int x0) (real_of_int x1)) = (real_of_num x2)) \/ ((real_add (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num x2))).
Definition term399 := real_div (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term601 (x0 : nat) := real_neg (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)).
Definition term454 := Nat.add (BIT1 0) (BIT1 0).
Definition term568 (x0 : nat) := real_sub (real_of_num x0).
Definition term442 (x0 : nat) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_of_num x0).
Definition term31 (x0 : real) (x1 : real) := (fun y0 : real => (real_add (real_neg x0) (real_neg y0)) = (real_neg (real_add x0 y0))) x1.
Definition term423 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.mul x0 x1)).
Definition term625 (x0 : nat) := ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL 0))).
Definition term623 (x0 : nat) := ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0)) (real_of_num (NUMERAL 0))).
Definition term55 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) \/ (Peano.le y1 y0)) x0.
Definition term51 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) = (exists y2 : nat, y1 = (Nat.add y0 y2))) x0.
Definition term49 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_of_num (Nat.add y0 y1)) = (real_add (real_of_num y0) (real_of_num y1))) x0.
Definition term22 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1))) x0.
Definition term19 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((real_of_num y0) = (real_of_num y1)) = (y0 = y1)) x0.
Definition term481 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term380 (x0 : nat) (x1 : nat) := @eq real (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))).
Definition term293 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_neg (real_of_num y0)).
Definition term133 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_add (real_neg (real_of_num x0)) (real_of_num x1)) = (real_neg (real_of_num y0)).
Definition term88 (x0 : int) (x1 : int) := fun y0 : nat => (real_add (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y0)).
Definition term729 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0)).
Definition term357 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0)).
Definition term326 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y0)).
Definition term262 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_neg (real_of_num y0)).
Definition term229 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0)).
Definition term196 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y0)).
Definition term141 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0)).
Definition term124 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_add (real_of_num x0) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0)).
Definition term621 (x0 : nat) := ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0)) (real_of_num (NUMERAL 0)))).
Definition term217 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.add x0 x1)).
Definition term70 (x0 : int) (x1 : int) := @eq real (real_of_int (int_of_real (real_add (real_of_int x0) (real_of_int x1)))).
Definition term328 (x0 : nat) (x1 : nat) := real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1))).
Definition term110 (x0 : nat) := real_add (real_of_num x0).
Definition term584 (x0 : nat) := real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0).
Definition term395 (x0 : nat) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0).
Definition term517 (x0 : nat) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num x0).
Definition term490 (x0 : nat) := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0).
Definition term507 (x0 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0))).
Definition term525 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term393 (x0 : nat) (x1 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_add (real_of_num x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1))).
Definition term12 (x0 : real) := forall y0 : real, (real_neg (real_add x0 y0)) = (real_add (real_neg x0) (real_neg y0)).
Definition term637 (x0 : nat) (x1 : nat) := ~ ((real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) = (real_of_num x1)).
Definition term387 (x0 : nat) (x1 : nat) := ~ ((real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num x1)).
Definition term390 (x0 : nat) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)).
Definition term127 (x0 : nat) := real_add (real_neg (real_of_num x0)).
Definition term682 (x0 : nat) (x1 : nat) := real_sub (real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term627 (x0 : nat) := or (((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL 0)))).
Definition term486 := real_div (real_of_num (NUMERAL (BIT0 (BIT1 0)))).
Definition term556 (x0 : nat) := (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term546 (x0 : nat) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term419 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term381 (x0 : nat) (x1 : nat) (x2 : nat) := or ((real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_of_num x2)).
Definition term372 (x0 : nat) (x1 : nat) (x2 : nat) := or ((real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_of_num x2)).
Definition term341 (x0 : nat) (x1 : nat) (x2 : nat) := or ((real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num x2)).
Definition term277 (x0 : nat) (x1 : nat) (x2 : nat) := or ((real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_of_num x2)).
Definition term255 (x0 : nat) (x1 : nat) (x2 : nat) := or ((real_add (real_add (real_of_num x1) (real_of_num x0)) (real_neg (real_of_num x1))) = (real_of_num x2)).
Definition term244 (x0 : nat) (x1 : nat) (x2 : nat) := or ((real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_of_num x2)).
Definition term211 (x0 : nat) (x1 : nat) (x2 : nat) := or ((real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num x2)).
Definition term436 (x0 : real) := real_div x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term23 (x0 : nat) := forall y0 : nat, (real_add (real_of_num x0) (real_of_num y0)) = (real_of_num (Nat.add x0 y0)).
Definition term433 (x0 : nat) := real_mul (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term398 := real_of_num (NUMERAL (BIT1 0)).
Definition term455 := BIT0 (BIT1 0).
Definition term689 (x0 : nat) (x1 : nat) := or (real_gt (real_sub (real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num (NUMERAL 0))).
Definition term659 (x0 : nat) (x1 : nat) := or (real_gt (real_sub (real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) (real_neg (real_of_num x1))) (real_of_num (NUMERAL 0))).
Definition term616 (x0 : nat) (x1 : nat) := or (real_gt (real_sub (real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) (real_of_num (NUMERAL 0))).
Definition term534 (x0 : nat) (x1 : nat) := or (real_gt (real_sub (real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) (real_neg (real_of_num x1))) (real_of_num (NUMERAL 0))).
Definition term643 (x0 : nat) (x1 : nat) := real_neg (real_sub (real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) (real_of_num x1)).
Definition term472 (x0 : nat) (x1 : nat) := real_neg (real_sub (real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) (real_of_num x1)).
Definition term642 (x0 : nat) (x1 : nat) := real_sub (real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) (real_of_num x1).
Definition term731 (x0 : nat) (x1 : nat) (x2 : nat) := or ((fun y0 : nat => (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_of_num y0)) x2).
Definition term699 (x0 : nat) (x1 : nat) (x2 : nat) := or ((fun y0 : nat => (real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num y0)) x2).
Definition term371 (x0 : nat) (x1 : nat) (x2 : nat) := or ((fun y0 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_of_num y0)) x2).
Definition term340 (x0 : nat) (x1 : nat) (x2 : nat) := or ((fun y0 : nat => (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y0)) x2).
Definition term307 (x0 : nat) (x1 : nat) (x2 : nat) := or ((fun y0 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_of_num y0)) x2).
Definition term276 (x0 : nat) (x1 : nat) (x2 : nat) := or ((fun y0 : nat => (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_of_num y0)) x2).
Definition term243 (x0 : nat) (x1 : nat) (x2 : nat) := or ((fun y0 : nat => (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_of_num y0)) x2).
Definition term210 (x0 : nat) (x1 : nat) (x2 : nat) := or ((fun y0 : nat => (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y0)) x2).
Definition term90 (x0 : int) (x1 : int) (x2 : nat) := or ((fun y0 : nat => (real_add (real_of_int x0) (real_of_int x1)) = (real_of_num y0)) x2).
Definition term506 (x0 : nat) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)).
Definition term640 (x0 : nat) (x1 : nat) := real_add (real_of_num x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1)) (real_of_num x1)).
Definition term505 (x0 : nat) (x1 : nat) := real_sub (real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) (real_neg (real_of_num x1)).
Definition term585 := real_add (real_of_num (NUMERAL (BIT1 0))).
Definition term9 (x0 : real) (x1 : real) := real_add (real_neg x0) (real_neg x1).
Definition term484 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0))).
Definition term598 := real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term607 := real_neg (real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT0 (BIT1 0))))).
Definition term551 := (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) -> (real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))) = (real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0))))).
Definition term284 (x0 : nat) (x1 : nat) := @eq real (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))).
Definition term715 (x0 : nat) (x1 : nat) := real_add (real_of_num x0) (real_of_num (Nat.add x0 x1)).
Definition term653 (x0 : nat) (x1 : nat) := real_neg (real_sub (real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) (real_neg (real_of_num x1))).
Definition term519 (x0 : nat) (x1 : nat) := real_neg (real_sub (real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) (real_neg (real_of_num x1))).
Definition term458 := real_of_num (Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term724 (x0 : nat) (x1 : nat) := exists y0 : nat, (Nat.add x0 (Nat.add x0 x1)) = y0.
Definition term73 (x0 : real) := exists y0 : nat, (x0 = (real_of_num y0)) \/ (x0 = (real_neg (real_of_num y0))).
Definition term535 := or (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term669 (x0 : nat) (x1 : nat) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num x1))) (real_of_num x1).
Definition term40 := fun y0 : nat => forall y1 : nat, (real_add (real_of_num y0) (real_of_num y1)) = (real_of_num (Nat.add y0 y1)).
Definition term314 (x0 : nat) (x1 : nat) := real_add (real_neg (real_of_num (Nat.add x0 x1))).
Definition term417 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term65 (x0 : int) (x1 : int) := (fun y0 : int => (int_add x0 y0) = (int_of_real (real_add (real_of_int x0) (real_of_int y0)))) x1.
Definition term251 (x0 : nat) (x1 : nat) := real_add (real_add (real_of_num x0) (real_of_num x1)).
Definition term78 (x0 : int) := forall y0 : int, exists y1 : nat, ((real_add (real_of_int x0) (real_of_int y0)) = (real_of_num y1)) \/ ((real_add (real_of_int x0) (real_of_int y0)) = (real_neg (real_of_num y1))).
Definition term118 (x0 : nat) (x1 : nat) := (exists y0 : nat, (Nat.add x0 x1) = y0) \/ (exists y0 : nat, (real_of_num (Nat.add x0 x1)) = (real_neg (real_of_num y0))).
Definition term83 (x0 : nat -> Prop) (x1 : nat -> Prop) := exists y0 : nat, (x0 y0) \/ (x1 y0).
Definition term283 (x0 : nat) (x1 : nat) := real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1)).
Definition term348 (x0 : nat) (x1 : nat) := @eq real (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))).
Definition term1 (a0 : Type') (x0 : a0) := fun y0 : a0 => x0 = y0.
Definition term378 (x0 : nat) (x1 : nat) := real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1)).
Definition term593 := real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term683 (x0 : nat) (x1 : nat) := real_neg (real_sub (real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) (real_neg (real_of_num x1))).
Definition term685 (x0 : nat) (x1 : nat) := real_gt (real_neg (real_sub (real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) (real_neg (real_of_num x1)))).
Definition term655 (x0 : nat) (x1 : nat) := real_gt (real_neg (real_sub (real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) (real_neg (real_of_num x1)))).
Definition term612 (x0 : nat) (x1 : nat) := real_gt (real_neg (real_sub (real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1)))).
Definition term528 (x0 : nat) (x1 : nat) := real_gt (real_neg (real_sub (real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) (real_neg (real_of_num x1)))).
Definition term734 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_of_num y1)) y0) \/ ((fun y1 : nat => (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y1))) y0).
Definition term702 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num y1)) y0) \/ ((fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_neg (real_of_num y1))) y0).
Definition term375 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_of_num y1)) y0) \/ ((fun y1 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y1))) y0).
Definition term344 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y1)) y0) \/ ((fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y1))) y0).
Definition term311 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_of_num y1)) y0) \/ ((fun y1 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_neg (real_of_num y1))) y0).
Definition term280 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_of_num y1)) y0) \/ ((fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_neg (real_of_num y1))) y0).
Definition term247 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_of_num y1)) y0) \/ ((fun y1 : nat => (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num y1))) y0).
Definition term214 (x0 : nat) (x1 : nat) := fun y0 : nat => ((fun y1 : nat => (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y1)) y0) \/ ((fun y1 : nat => (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y1))) y0).
Definition term96 (x0 : int) (x1 : int) := fun y0 : nat => ((fun y1 : nat => (real_add (real_of_int x0) (real_of_int x1)) = (real_of_num y1)) y0) \/ ((fun y1 : nat => (real_add (real_of_int x0) (real_of_int x1)) = (real_neg (real_of_num y1))) y0).
Definition term740 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (fun y1 : nat => (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_neg (real_of_num x1))) = (real_of_num y1)) y0).
Definition term708 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num y1)) y0).
Definition term363 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_of_num y1)) y0).
Definition term332 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y1)) y0).
Definition term299 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_of_num y1)) y0).
Definition term268 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_of_num y1)) y0).
Definition term235 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (fun y1 : nat => (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_of_num y1)) y0).
Definition term202 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (fun y1 : nat => (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y1)) y0).
Definition term103 (x0 : int) (x1 : int) := or (exists y0 : nat, (fun y1 : nat => (real_add (real_of_int x0) (real_of_int x1)) = (real_of_num y1)) y0).
Definition term128 (x0 : nat) (x1 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x1).
Definition term53 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) = (exists y1 : nat, y0 = (Nat.add x0 y1))) x1.
Definition term673 (x0 : nat) (x1 : nat) := real_neg (real_sub (real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) (real_of_num x1)).
Definition term549 := real_lt (real_div (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term405 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term446 := real_add (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term397 (x0 : nat) := real_div (real_of_num x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term115 (x0 : nat) (x1 : nat) := or (exists y0 : nat, (Nat.add x0 x1) = y0).
Definition term477 := real_mul (real_div (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term318 (x0 : nat) (x1 : nat) := @eq real (real_add (real_add (real_neg (real_of_num x1)) (real_neg (real_of_num x0))) (real_of_num x1)).
Definition term21 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((real_of_num x0) = (real_of_num y0)) = (x0 = y0)) x1.
Definition term603 (x0 : nat) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0).
Definition term38 (x0 : nat) := fun y0 : nat => (real_of_num (Nat.add x0 y0)) = (real_add (real_of_num x0) (real_of_num y0)).
Definition term629 (x0 : nat) := (((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL 0))))) \/ (((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0)) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0)) (real_of_num (NUMERAL 0))))).
Definition term545 (x0 : nat) := (((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))))) \/ (((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))))).
Definition term347 (x0 : nat) (x1 : nat) := real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))).
Definition term526 := real_div (real_of_num (NUMERAL 0)).
Definition term26 (x0 : nat) (x1 : nat) := real_of_num (Nat.add x0 x1).
Definition term35 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term34 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (exists y1 : a0, (x0 y1) \/ (y0 y1)) = ((exists y1 : a0, x0 y1) \/ (exists y1 : a0, y0 y1))) x1.
Definition term675 (x0 : nat) (x1 : nat) := real_gt (real_neg (real_sub (real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) (real_of_num x1))).
Definition term645 (x0 : nat) (x1 : nat) := real_gt (real_neg (real_sub (real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) (real_of_num x1))).
Definition term573 (x0 : nat) (x1 : nat) := real_gt (real_neg (real_sub (real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) (real_of_num x1))).
Definition term492 (x0 : nat) (x1 : nat) := real_gt (real_neg (real_sub (real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) (real_of_num x1))).
Definition term575 (x0 : nat) (x1 : nat) := real_gt (real_sub (real_add (real_add (real_of_num x0) (real_of_num x1)) (real_neg (real_of_num x0))) (real_of_num x1)).
Definition term596 := real_mul (real_add (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term462 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term431 := real_mul (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0))))) (real_of_num (NUMERAL (BIT1 0))).
Definition term483 := Nat.mul (BIT1 0) (BIT0 (BIT1 0)).
Definition term663 (x0 : nat) (x1 : nat) := ((real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) = (real_of_num x1)) \/ ((real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) = (real_neg (real_of_num x1))).
Definition term559 (x0 : nat) (x1 : nat) := ((real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_of_num x1)) \/ ((real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_neg (real_of_num x1))).
Definition term697 (x0 : nat) (x1 : nat) := fun y0 : nat => (real_add (real_neg (real_of_num x0)) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_neg (real_of_num y0)).
Definition term252 (x0 : nat) (x1 : nat) := real_add (real_add (real_of_num x1) (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term41 := fun y0 : nat => forall y1 : nat, (real_of_num (Nat.add y0 y1)) = (real_add (real_of_num y0) (real_of_num y1)).
Definition term400 := NUMERAL (BIT1 0).
Definition term84 (x0 : nat -> Prop) (x1 : nat -> Prop) := (exists y0 : nat, x0 y0) \/ (exists y0 : nat, x1 y0).
Definition term218 (x0 : nat) (x1 : nat) := real_neg (real_add (real_of_num x0) (real_of_num x1)).
Definition term677 (x0 : nat) (x1 : nat) := real_gt (real_sub (real_add (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) (real_of_num x0)) (real_of_num x1)).
Definition term497 (x0 : nat) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0)).
Definition term650 (x0 : nat) (x1 : nat) := ~ ((real_add (real_neg (real_of_num x0)) (real_add (real_of_num x0) (real_of_num x1))) = (real_neg (real_of_num x1))).
Definition term503 (x0 : nat) (x1 : nat) := ~ ((real_add (real_of_num x0) (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1)))) = (real_neg (real_of_num x1))).
Definition term15 := fun y0 : real => forall y1 : real, (real_add (real_neg y0) (real_neg y1)) = (real_neg (real_add y0 y1)).
Definition term539 (x0 : nat) := ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_of_num x0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_of_num x0)) (real_of_num (NUMERAL 0)))) /\ ((real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term606 := real_div (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT0 (BIT1 0))))) (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term554 := real_lt (real_mul (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL (BIT1 0)))).
Definition term755 (x0 : nat) (x1 : nat) := fun y0 : nat => (Nat.add (Nat.add x1 x0) x1) = y0.
Definition term529 := real_gt (real_of_num (NUMERAL 0)).
Definition term370 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0)))).
Definition term369 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_of_num y1)) y0) \/ (exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_neg (real_of_num x1))) = (real_neg (real_of_num y1))) y0)).
Definition term339 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y0)))).
Definition term338 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y1)) y0) \/ (exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y1))) y0)).
Definition term306 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_neg (real_of_num y0)))).
Definition term305 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_of_num y1)) y0) \/ (exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1)) = (real_neg (real_of_num y1))) y0)).
Definition term275 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_neg (real_of_num y0)))).
Definition term274 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_of_num y1)) y0) \/ (exists y0 : nat, (fun y1 : nat => (real_add (real_neg (real_of_num x0)) (real_of_num (Nat.add x0 x1))) = (real_neg (real_of_num y1))) y0)).
Definition term242 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0)))).
Definition term241 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_of_num y1)) y0) \/ (exists y0 : nat, (fun y1 : nat => (real_add (real_of_num (Nat.add x1 x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num y1))) y0)).
Definition term209 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y0)))).
Definition term208 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (fun y1 : nat => (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_of_num y1)) y0) \/ (exists y0 : nat, (fun y1 : nat => (real_add (real_of_num x0) (real_neg (real_of_num (Nat.add x0 x1)))) = (real_neg (real_of_num y1))) y0)).
Definition term187 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0)))).
Definition term176 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num x1)) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_neg (real_of_num x0)) (real_of_num x1)) = (real_neg (real_of_num y0)))).
Definition term165 (x0 : nat) (x1 : nat) := @eq Prop ((exists y0 : nat, (real_add (real_of_num x0) (real_neg (real_of_num x1))) = (real_of_num y0)) \/ (exists y0 : nat, (real_add (real_of_num x0) (real_neg (real_of_num x1))) = (real_neg (real_of_num y0)))).
