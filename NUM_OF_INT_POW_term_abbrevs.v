Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term14 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := (fun y0 : type1413 a0 a1 => (forall y1 : a0, forall y2 : a1, y0 y1 y2) = (forall y1 : a1, forall y2 : a0, y0 y2 y1)) x0.
Definition term25 (x0 : int) (x1 : nat) := (fun y0 : nat => (int_le (int_of_num (NUMERAL 0)) x0) -> (num_of_int (int_pow x0 y0)) = (Nat.pow (num_of_int x0) y0)) x1.
Definition term48 (x0 : int) := imp (int_le (int_of_num (NUMERAL 0)) x0).
Definition term59 (x0 : nat) (x1 : nat) := num_of_int (int_of_num (Nat.pow x0 x1)).
Definition term21 := fun y0 : int => fun y1 : nat => (int_le (int_of_num (NUMERAL 0)) y0) -> (num_of_int (int_pow y0 y1)) = (Nat.pow (num_of_int y0) y1).
Definition term65 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term13 (x0 : int -> Prop) := (fun y0 : int -> Prop => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : nat, y0 (int_of_num y1))) x0.
Definition term27 (x0 : int) := fun y0 : nat => (fun y1 : int => fun y2 : nat => (int_le (int_of_num (NUMERAL 0)) y1) -> (num_of_int (int_pow y1 y2)) = (Nat.pow (num_of_int y1) y2)) x0 y0.
Definition term38 (x0 : nat) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (num_of_int (int_pow y0 x0)) = (Nat.pow (num_of_int y0) x0).
Definition term44 (x0 : nat) := fun y0 : int => (num_of_int (int_pow y0 x0)) = (Nat.pow (num_of_int y0) x0).
Definition term36 (x0 : nat) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> (num_of_int (int_pow y0 x0)) = (Nat.pow (num_of_int y0) x0).
Definition term15 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a0, forall y1 : a1, x0 y0 y1.
Definition term28 (x0 : int) := forall y0 : nat, (fun y1 : int => fun y2 : nat => (int_le (int_of_num (NUMERAL 0)) y1) -> (num_of_int (int_pow y1 y2)) = (Nat.pow (num_of_int y1) y2)) x0 y0.
Definition term30 := fun y0 : int => forall y1 : nat, (fun y2 : int => fun y3 : nat => (int_le (int_of_num (NUMERAL 0)) y2) -> (num_of_int (int_pow y2 y3)) = (Nat.pow (num_of_int y2) y3)) y0 y1.
Definition term26 (x0 : int) (x1 : nat) := (int_le (int_of_num (NUMERAL 0)) x0) -> (num_of_int (int_pow x0 x1)) = (Nat.pow (num_of_int x0) x1).
Definition term58 (x0 : nat) := forall y0 : nat, (num_of_int (int_pow (int_of_num y0) x0)) = (Nat.pow (num_of_int (int_of_num y0)) x0).
Definition term56 (x0 : nat) := fun y0 : nat => (fun y1 : int => (num_of_int (int_pow y1 x0)) = (Nat.pow (num_of_int y1) x0)) (int_of_num y0).
Definition term45 (x0 : nat) (x1 : int) := (fun y0 : int => (num_of_int (int_pow y0 x0)) = (Nat.pow (num_of_int y0) x0)) x1.
Definition term46 (x0 : int) (x1 : nat) := num_of_int (int_pow x0 x1).
Definition term52 (x0 : nat) := @eq Prop (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (num_of_int (int_pow y0 x0)) = (Nat.pow (num_of_int y0) x0)).
Definition term51 (x0 : nat) := @eq Prop (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => (num_of_int (int_pow y1 x0)) = (Nat.pow (num_of_int y1) x0)) y0).
Definition term54 (x0 : nat) (x1 : nat) := num_of_int (int_pow (int_of_num x0) x1).
Definition term29 (x0 : int) := forall y0 : nat, (int_le (int_of_num (NUMERAL 0)) x0) -> (num_of_int (int_pow x0 y0)) = (Nat.pow (num_of_int x0) y0).
Definition term5 := forall y0 : int -> Prop, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : nat, y0 (int_of_num y1)).
Definition term4 := forall y0 : int -> Prop, (forall y1 : nat, y0 (int_of_num y1)) = (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1).
Definition term62 (x0 : nat) := Nat.pow (num_of_int (int_of_num x0)).
Definition term12 (x0 : nat) (x1 : nat) := int_of_num (Nat.pow x0 x1).
Definition term3 := fun y0 : int -> Prop => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : nat, y0 (int_of_num y1)).
Definition term2 := fun y0 : int -> Prop => (forall y1 : nat, y0 (int_of_num y1)) = (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1).
Definition term41 := forall y0 : nat, forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (num_of_int (int_pow y1 y0)) = (Nat.pow (num_of_int y1) y0).
Definition term20 := forall y0 : nat, forall y1 : int, (fun y2 : int => fun y3 : nat => (int_le (int_of_num (NUMERAL 0)) y2) -> (num_of_int (int_pow y2 y3)) = (Nat.pow (num_of_int y2) y3)) y1 y0.
Definition term18 (x0 : type1552) := forall y0 : nat, forall y1 : int, x0 y1 y0.
Definition term55 (x0 : nat) (x1 : nat) := Nat.pow (num_of_int (int_of_num x0)) x1.
Definition term34 := @eq Prop (forall y0 : int, forall y1 : nat, (int_le (int_of_num (NUMERAL 0)) y0) -> (num_of_int (int_pow y0 y1)) = (Nat.pow (num_of_int y0) y1)).
Definition term33 := @eq Prop (forall y0 : int, forall y1 : nat, (fun y2 : int => fun y3 : nat => (int_le (int_of_num (NUMERAL 0)) y2) -> (num_of_int (int_pow y2 y3)) = (Nat.pow (num_of_int y2) y3)) y0 y1).
Definition term16 (a0 : Type') (a1 : Type') (x0 : type1413 a0 a1) := forall y0 : a1, forall y1 : a0, x0 y1 y0.
Definition term49 (x0 : nat) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> (fun y0 : int => (num_of_int (int_pow y0 x0)) = (Nat.pow (num_of_int y0) x0)) x1.
Definition term50 (x0 : nat) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => (num_of_int (int_pow y1 x0)) = (Nat.pow (num_of_int y1) x0)) y0.
Definition term9 (x0 : nat) := forall y0 : nat, (int_pow (int_of_num x0) y0) = (int_of_num (Nat.pow x0 y0)).
Definition term1 (x0 : int -> Prop) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> x0 y0.
Definition term64 := forall y0 : nat, True.
Definition term32 := forall y0 : int, forall y1 : nat, (int_le (int_of_num (NUMERAL 0)) y0) -> (num_of_int (int_pow y0 y1)) = (Nat.pow (num_of_int y0) y1).
Definition term19 := forall y0 : int, forall y1 : nat, (fun y2 : int => fun y3 : nat => (int_le (int_of_num (NUMERAL 0)) y2) -> (num_of_int (int_pow y2 y3)) = (Nat.pow (num_of_int y2) y3)) y0 y1.
Definition term17 (x0 : type1552) := forall y0 : int, forall y1 : nat, x0 y0 y1.
Definition term63 := fun y0 : nat => True.
Definition term60 (x0 : nat) (x1 : nat) := @eq nat (num_of_int (int_pow (int_of_num x0) x1)).
Definition term35 (x0 : nat) := fun y0 : int => (fun y1 : int => fun y2 : nat => (int_le (int_of_num (NUMERAL 0)) y1) -> (num_of_int (int_pow y1 y2)) = (Nat.pow (num_of_int y1) y2)) y0 x0.
Definition term61 (x0 : nat) (x1 : nat) := @eq nat (Nat.pow x0 x1).
Definition term39 := fun y0 : nat => forall y1 : int, (fun y2 : int => fun y3 : nat => (int_le (int_of_num (NUMERAL 0)) y2) -> (num_of_int (int_pow y2 y3)) = (Nat.pow (num_of_int y2) y3)) y1 y0.
Definition term40 := fun y0 : nat => forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> (num_of_int (int_pow y1 y0)) = (Nat.pow (num_of_int y1) y0).
Definition term8 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (int_pow (int_of_num y0) y1) = (int_of_num (Nat.pow y0 y1))) x0.
Definition term57 (x0 : nat) := fun y0 : nat => (num_of_int (int_pow (int_of_num y0) x0)) = (Nat.pow (num_of_int (int_of_num y0)) x0).
Definition term7 (x0 : nat) := num_of_int (int_of_num x0).
Definition term0 (x0 : int -> Prop) := forall y0 : nat, x0 (int_of_num y0).
Definition term47 (x0 : int) (x1 : nat) := Nat.pow (num_of_int x0) x1.
Definition term43 (x0 : nat) := forall y0 : nat, (fun y1 : int => (num_of_int (int_pow y1 x0)) = (Nat.pow (num_of_int y1) x0)) (int_of_num y0).
Definition term24 (x0 : int) (x1 : nat) := (fun y0 : int => fun y1 : nat => (int_le (int_of_num (NUMERAL 0)) y0) -> (num_of_int (int_pow y0 y1)) = (Nat.pow (num_of_int y0) y1)) x0 x1.
Definition term11 (x0 : nat) (x1 : nat) := int_pow (int_of_num x0) x1.
Definition term23 (x0 : int) := fun y0 : nat => (int_le (int_of_num (NUMERAL 0)) x0) -> (num_of_int (int_pow x0 y0)) = (Nat.pow (num_of_int x0) y0).
Definition term53 (x0 : nat) (x1 : nat) := (fun y0 : int => (num_of_int (int_pow y0 x0)) = (Nat.pow (num_of_int y0) x0)) (int_of_num x1).
Definition term42 (x0 : nat) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => (num_of_int (int_pow y1 x0)) = (Nat.pow (num_of_int y1) x0)) y0.
Definition term37 (x0 : nat) := forall y0 : int, (fun y1 : int => fun y2 : nat => (int_le (int_of_num (NUMERAL 0)) y1) -> (num_of_int (int_pow y1 y2)) = (Nat.pow (num_of_int y1) y2)) y0 x0.
Definition term66 (x0 : Prop) := forall y0 : nat, x0.
Definition term22 (x0 : int) := (fun y0 : int => fun y1 : nat => (int_le (int_of_num (NUMERAL 0)) y0) -> (num_of_int (int_pow y0 y1)) = (Nat.pow (num_of_int y0) y1)) x0.
Definition term6 (x0 : nat) := (fun y0 : nat => (num_of_int (int_of_num y0)) = y0) x0.
Definition term31 := fun y0 : int => forall y1 : nat, (int_le (int_of_num (NUMERAL 0)) y0) -> (num_of_int (int_pow y0 y1)) = (Nat.pow (num_of_int y0) y1).
Definition term10 (x0 : nat) (x1 : nat) := (fun y0 : nat => (int_pow (int_of_num x0) y0) = (int_of_num (Nat.pow x0 y0))) x1.
