Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term26 (x0 : nat) (x1 : real) := fun y0 : nat => (@sum nat (dotdot x0 y0) (fun y1 : nat => x1)) = (real_mul (real_of_num (Nat.sub (Nat.add y0 (NUMERAL (BIT1 0))) x0)) x1).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) := real_mul (real_of_num (@CARD a0 x0)) x1.
Definition term30 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term35 := fun y0 : real => True.
Definition term4 (x0 : nat) (x1 : nat) := Nat.sub (Nat.add x0 (NUMERAL (BIT1 0))) x1.
Definition term18 (x0 : nat) (x1 : nat) (x2 : real) := real_mul (real_of_num (@CARD nat (dotdot x0 x1))) x2.
Definition term37 := forall y0 : real, True.
Definition term38 (x0 : Prop) := forall y0 : real, x0.
Definition term36 := forall y0 : real, forall y1 : nat, forall y2 : nat, (@sum nat (dotdot y1 y2) (fun y3 : nat => y0)) = (real_mul (real_of_num (Nat.sub (Nat.add y2 (NUMERAL (BIT1 0))) y1)) y0).
Definition term6 (x0 : nat) := forall y0 : nat, @FINITE nat (dotdot x0 y0).
Definition term16 (x0 : nat) (x1 : nat) (x2 : real) := (@FINITE nat (dotdot x0 x1)) -> (@sum nat (dotdot x0 x1) (fun y0 : nat => x2)) = (real_mul (real_of_num (@CARD nat (dotdot x0 x1))) x2).
Definition term10 (a0 : Type') (x0 : real) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (@sum a0 y0 (fun y1 : a0 => x0)) = (real_mul (real_of_num (@CARD a0 y0)) x0).
Definition term25 (x0 : nat) (x1 : nat) (x2 : real) := @eq real (real_mul (real_of_num (Nat.sub (Nat.add x0 (NUMERAL (BIT1 0))) x1)) x2).
Definition term7 (x0 : nat) (x1 : nat) := (fun y0 : nat => @FINITE nat (dotdot x0 y0)) x1.
Definition term32 (x0 : real) := fun y0 : nat => forall y1 : nat, (@sum nat (dotdot y0 y1) (fun y2 : nat => x0)) = (real_mul (real_of_num (Nat.sub (Nat.add y1 (NUMERAL (BIT1 0))) y0)) x0).
Definition term1 (x0 : nat) := forall y0 : nat, (@CARD nat (dotdot x0 y0)) = (Nat.sub (Nat.add y0 (NUMERAL (BIT1 0))) x0).
Definition term11 (a0 : Type') (x0 : real) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (@sum a0 y0 (fun y1 : a0 => x0)) = (real_mul (real_of_num (@CARD a0 y0)) x0)) x1.
Definition term33 (x0 : real) := forall y0 : nat, forall y1 : nat, (@sum nat (dotdot y0 y1) (fun y2 : nat => x0)) = (real_mul (real_of_num (Nat.sub (Nat.add y1 (NUMERAL (BIT1 0))) y0)) x0).
Definition term29 := forall y0 : nat, True.
Definition term23 (x0 : nat) (x1 : nat) (x2 : real) := real_mul (real_of_num (Nat.sub (Nat.add x0 (NUMERAL (BIT1 0))) x1)) x2.
Definition term3 (x0 : nat) (x1 : nat) := @CARD nat (dotdot x0 x1).
Definition term27 := fun y0 : nat => True.
Definition term13 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) := @sum a0 x0 (fun y0 : a0 => x1).
Definition term17 (x0 : nat) (x1 : nat) (x2 : real) := @sum nat (dotdot x0 x1) (fun y0 : nat => x2).
Definition term15 (x0 : nat -> Prop) (x1 : real) := (@FINITE nat x0) -> (@sum nat x0 (fun y0 : nat => x1)) = (real_mul (real_of_num (@CARD nat x0)) x1).
Definition term12 (a0 : Type') (x0 : a0 -> Prop) (x1 : real) := (@FINITE a0 x0) -> (@sum a0 x0 (fun y0 : a0 => x1)) = (real_mul (real_of_num (@CARD a0 x0)) x1).
Definition term24 (x0 : nat) (x1 : nat) (x2 : real) := @eq real (@sum nat (dotdot x0 x1) (fun y0 : nat => x2)).
Definition term8 (x0 : nat) (x1 : nat) := @FINITE nat (dotdot x0 x1).
Definition term34 := fun y0 : real => forall y1 : nat, forall y2 : nat, (@sum nat (dotdot y1 y2) (fun y3 : nat => y0)) = (real_mul (real_of_num (Nat.sub (Nat.add y2 (NUMERAL (BIT1 0))) y1)) y0).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (@CARD nat (dotdot y0 y1)) = (Nat.sub (Nat.add y1 (NUMERAL (BIT1 0))) y0)) x0.
Definition term5 (x0 : nat) := (fun y0 : nat => forall y1 : nat, @FINITE nat (dotdot y0 y1)) x0.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (@CARD nat (dotdot x0 y0)) = (Nat.sub (Nat.add y0 (NUMERAL (BIT1 0))) x0)) x1.
Definition term31 (x0 : Prop) := forall y0 : nat, x0.
Definition term21 (x0 : nat) (x1 : nat) := real_mul (real_of_num (@CARD nat (dotdot x0 x1))).
Definition term19 (x0 : nat) (x1 : nat) := real_of_num (@CARD nat (dotdot x0 x1)).
Definition term22 (x0 : nat) (x1 : nat) := real_mul (real_of_num (Nat.sub (Nat.add x0 (NUMERAL (BIT1 0))) x1)).
Definition term20 (x0 : nat) (x1 : nat) := real_of_num (Nat.sub (Nat.add x0 (NUMERAL (BIT1 0))) x1).
Definition term9 (a0 : Type') (x0 : real) := (fun y0 : real => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (@sum a0 y1 (fun y2 : a0 => y0)) = (real_mul (real_of_num (@CARD a0 y1)) y0)) x0.
Definition term28 (x0 : nat) (x1 : real) := forall y0 : nat, (@sum nat (dotdot x0 y0) (fun y1 : nat => x1)) = (real_mul (real_of_num (Nat.sub (Nat.add y0 (NUMERAL (BIT1 0))) x0)) x1).
