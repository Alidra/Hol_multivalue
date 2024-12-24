Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term67 := (~ False) -> False.
Definition term14 (x0 : int) := imp (int_le (int_of_num (NUMERAL 0)) x0).
Definition term15 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> (fun y0 : int => (int_of_num (num_of_int y0)) = y0) x0.
Definition term19 := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (int_of_num (num_of_int y0)) = y0.
Definition term47 (x0 : Prop) := ~ (~ x0).
Definition term60 (x0 : nat) := forall y0 : nat, ~ ((int_of_num y0) = (int_of_num x0)).
Definition term51 := forall y0 : nat, exists y1 : nat, (int_of_num y1) = (int_of_num y0).
Definition term28 (x0 : nat) := @ε nat (fun y0 : nat => (int_of_num y0) = (int_of_num x0)).
Definition term62 (x0 : nat) := (~ ((int_of_num x0) = (int_of_num x0))) -> (int_of_num x0) = (int_of_num x0).
Definition term8 (x0 : int -> Prop) := (fun y0 : int -> Prop => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : nat, y0 (int_of_num y1))) x0.
Definition term40 (x0 : Prop) := (~ x0) -> False.
Definition term30 (x0 : nat) := @eq int (int_of_num (num_of_int (int_of_num x0))).
Definition term24 := fun y0 : nat => (fun y1 : int => (int_of_num (num_of_int y1)) = y1) (int_of_num y0).
Definition term38 (x0 : nat) := @eq Prop ((fun y0 : nat => (int_of_num y0) = (int_of_num x0)) (@ε nat (fun y0 : nat => (int_of_num y0) = (int_of_num x0)))).
Definition term6 (x0 : int) := (fun y0 : int => (num_of_int y0) = (@ε nat (fun y1 : nat => (int_of_num y1) = y0))) x0.
Definition term61 (x0 : nat) (x1 : nat) := (fun y0 : nat => ~ ((int_of_num y0) = (int_of_num x0))) x1.
Definition term64 (x0 : Prop) := (~ x0) -> x0.
Definition term66 (x0 : nat) := ((int_of_num x0) = (int_of_num x0)) -> False.
Definition term32 := fun y0 : nat => (int_of_num (@ε nat (fun y1 : nat => (int_of_num y1) = (int_of_num y0)))) = (int_of_num y0).
Definition term41 (x0 : nat) := (~ (exists y0 : nat, (int_of_num y0) = (int_of_num x0))) -> False.
Definition term33 := forall y0 : nat, (int_of_num (@ε nat (fun y1 : nat => (int_of_num y1) = (int_of_num y0)))) = (int_of_num y0).
Definition term26 := forall y0 : nat, (int_of_num (num_of_int (int_of_num y0))) = (int_of_num y0).
Definition term16 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> (int_of_num (num_of_int x0)) = x0.
Definition term7 (x0 : int) := @ε nat (fun y0 : nat => (int_of_num y0) = x0).
Definition term39 (x0 : nat) := @eq Prop ((int_of_num (@ε nat (fun y0 : nat => (int_of_num y0) = (int_of_num x0)))) = (int_of_num x0)).
Definition term21 := @eq Prop (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (int_of_num (num_of_int y0)) = y0).
Definition term20 := @eq Prop (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => (int_of_num (num_of_int y1)) = y1) y0).
Definition term35 (x0 : nat) := (fun y0 : nat => (int_of_num y0) = (int_of_num x0)) (@ε nat (fun y0 : nat => (int_of_num y0) = (int_of_num x0))).
Definition term49 := fun y0 : nat => exists y1 : nat, (int_of_num y1) = (int_of_num y0).
Definition term5 := forall y0 : int -> Prop, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : nat, y0 (int_of_num y1)).
Definition term4 := forall y0 : int -> Prop, (forall y1 : nat, y0 (int_of_num y1)) = (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1).
Definition term65 (x0 : nat) (x1 : nat) := ((int_of_num x0) = (int_of_num x1)) -> False.
Definition term43 (x0 : nat) := ((~ (exists y0 : nat, (int_of_num y0) = (int_of_num x0))) -> False) -> (~ (exists y0 : nat, (int_of_num y0) = (int_of_num x0))) -> False.
Definition term3 := fun y0 : int -> Prop => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : nat, y0 (int_of_num y1)).
Definition term2 := fun y0 : int -> Prop => (forall y1 : nat, y0 (int_of_num y1)) = (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1).
Definition term22 (x0 : nat) := (fun y0 : int => (int_of_num (num_of_int y0)) = y0) (int_of_num x0).
Definition term52 (x0 : nat -> Prop) := ~ (ex x0).
Definition term36 (x0 : nat) := exists y0 : nat, (int_of_num y0) = (int_of_num x0).
Definition term13 (x0 : int) := int_of_num (num_of_int x0).
Definition term48 := fun y0 : nat => (~ (exists y1 : nat, (int_of_num y1) = (int_of_num y0))) -> False.
Definition term68 (x0 : nat) := (fun y0 : nat => (~ (exists y1 : nat, (int_of_num y1) = (int_of_num y0))) -> False) x0.
Definition term1 (x0 : int -> Prop) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> x0 y0.
Definition term12 (x0 : int) := (fun y0 : int => (int_of_num (num_of_int y0)) = y0) x0.
Definition term53 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term34 (x0 : nat -> Prop) := x0 (@ε nat x0).
Definition term50 := forall y0 : nat, (~ (exists y1 : nat, (int_of_num y1) = (int_of_num y0))) -> False.
Definition term44 (x0 : nat) := (((~ (exists y0 : nat, (int_of_num y0) = (int_of_num x0))) -> False) -> (~ (exists y0 : nat, (int_of_num y0) = (int_of_num x0))) -> False) -> (~ (exists y0 : nat, (int_of_num y0) = (int_of_num x0))) -> False.
Definition term10 := forall y0 : nat, (fun y1 : int => (int_of_num (num_of_int y1)) = y1) (int_of_num y0).
Definition term37 (x0 : nat) := fun y0 : nat => (int_of_num y0) = (int_of_num x0).
Definition term54 (x0 : nat) := forall y0 : nat, ~ ((fun y1 : nat => (int_of_num y1) = (int_of_num x0)) y0).
Definition term27 (x0 : nat) := num_of_int (int_of_num x0).
Definition term0 (x0 : int -> Prop) := forall y0 : nat, x0 (int_of_num y0).
Definition term25 := fun y0 : nat => (int_of_num (num_of_int (int_of_num y0))) = (int_of_num y0).
Definition term9 := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => (int_of_num (num_of_int y1)) = y1) y0.
Definition term63 (x0 : nat) := ~ ((int_of_num x0) = (int_of_num x0)).
Definition term17 := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => (int_of_num (num_of_int y1)) = y1) y0.
Definition term23 (x0 : nat) := int_of_num (num_of_int (int_of_num x0)).
Definition term18 := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> (int_of_num (num_of_int y0)) = y0.
Definition term55 (x0 : nat) (x1 : nat) := (fun y0 : nat => (int_of_num y0) = (int_of_num x0)) x1.
Definition term58 (x0 : nat) := fun y0 : nat => ~ ((fun y1 : nat => (int_of_num y1) = (int_of_num x0)) y0).
Definition term56 (x0 : nat) (x1 : nat) := ~ ((fun y0 : nat => (int_of_num y0) = (int_of_num x0)) x1).
Definition term45 (x0 : nat) := (((~ (exists y0 : nat, (int_of_num y0) = (int_of_num x0))) -> False) -> (~ (exists y0 : nat, (int_of_num y0) = (int_of_num x0))) -> False) -> ((~ (exists y0 : nat, (int_of_num y0) = (int_of_num x0))) -> False) -> (~ (exists y0 : nat, (int_of_num y0) = (int_of_num x0))) -> False.
Definition term11 := fun y0 : int => (int_of_num (num_of_int y0)) = y0.
Definition term57 (x0 : nat) (x1 : nat) := ~ ((int_of_num x0) = (int_of_num x1)).
Definition term59 (x0 : nat) := fun y0 : nat => ~ ((int_of_num y0) = (int_of_num x0)).
Definition term46 (x0 : nat) := ~ (~ (exists y0 : nat, (int_of_num y0) = (int_of_num x0))).
Definition term31 (x0 : nat) := @eq int (int_of_num (@ε nat (fun y0 : nat => (int_of_num y0) = (int_of_num x0)))).
Definition term42 (x0 : nat) := ~ (exists y0 : nat, (int_of_num y0) = (int_of_num x0)).
Definition term29 (x0 : nat) := int_of_num (@ε nat (fun y0 : nat => (int_of_num y0) = (int_of_num x0))).
