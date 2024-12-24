Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term22 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, (int_divides y0 x0) -> (int_divides y1 (div x0 y0)) = (int_divides (int_mul y0 y1) x0)) x1.
Definition term25 (x0 : int) (x1 : int) (x2 : int) := (int_divides x0 x2) -> (int_divides x1 (div x2 x0)) = (int_divides (int_mul x0 x1) x2).
Definition term42 (x0 : nat) (x1 : nat) (x2 : nat) := num_divides (Nat.mul x0 x1) x2.
Definition term11 (x0 : nat) (x1 : nat) := int_of_num (Nat.div x0 x1).
Definition term3 (x0 : nat) := fun y0 : nat => (int_of_num (Nat.mul x0 y0)) = (int_mul (int_of_num x0) (int_of_num y0)).
Definition term53 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term39 (x0 : nat) (x1 : nat) (x2 : nat) := int_divides (int_of_num x0) (div (int_of_num x1) (int_of_num x2)).
Definition term34 (x0 : nat) (x1 : nat) := imp (num_divides x0 x1).
Definition term23 (x0 : int) (x1 : int) := forall y0 : int, (int_divides x0 x1) -> (int_divides y0 (div x1 x0)) = (int_divides (int_mul x0 y0) x1).
Definition term20 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (int_divides y1 y0) -> (int_divides y2 (div y0 y1)) = (int_divides (int_mul y1 y2) y0)) x0.
Definition term35 (x0 : nat) (x1 : nat) := imp (int_divides (int_of_num x0) (int_of_num x1)).
Definition term27 (x0 : nat) (x1 : nat) := (fun y0 : nat => (int_of_num (Nat.mul x0 y0)) = (int_mul (int_of_num x0) (int_of_num y0))) x1.
Definition term13 (x0 : nat) := fun y0 : nat => (int_of_num (Nat.div x0 y0)) = (div (int_of_num x0) (int_of_num y0)).
Definition term24 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (int_divides x0 x1) -> (int_divides y0 (div x1 x0)) = (int_divides (int_mul x0 y0) x1)) x2.
Definition term10 (x0 : nat) (x1 : nat) := div (int_of_num x0) (int_of_num x1).
Definition term51 (x0 : nat) (x1 : nat) := forall y0 : nat, (num_divides x0 x1) -> (num_divides y0 (Nat.div x1 x0)) = (num_divides (Nat.mul x0 y0) x1).
Definition term47 (x0 : nat) (x1 : nat) (x2 : nat) := (num_divides x0 x2) -> (num_divides x1 (Nat.div x2 x0)) = (num_divides (Nat.mul x0 x1) x2).
Definition term49 (x0 : nat) (x1 : nat) := fun y0 : nat => (num_divides x0 x1) -> (num_divides y0 (Nat.div x1 x0)) = (num_divides (Nat.mul x0 y0) x1).
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat) := num_divides x0 (Nat.div x1 x2).
Definition term38 (x0 : nat) := int_divides (int_of_num x0).
Definition term1 (x0 : nat) (x1 : nat) := int_of_num (Nat.mul x0 x1).
Definition term58 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (num_divides y1 y0) -> (num_divides y2 (Nat.div y0 y1)) = (num_divides (Nat.mul y1 y2) y0).
Definition term56 (x0 : nat) := forall y0 : nat, forall y1 : nat, (num_divides y0 x0) -> (num_divides y1 (Nat.div x0 y0)) = (num_divides (Nat.mul y0 y1) x0).
Definition term19 := forall y0 : nat, forall y1 : nat, (int_of_num (Nat.div y0 y1)) = (div (int_of_num y0) (int_of_num y1)).
Definition term18 := forall y0 : nat, forall y1 : nat, (div (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.div y0 y1)).
Definition term9 := forall y0 : nat, forall y1 : nat, (int_of_num (Nat.mul y0 y1)) = (int_mul (int_of_num y0) (int_of_num y1)).
Definition term8 := forall y0 : nat, forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1)).
Definition term15 (x0 : nat) := forall y0 : nat, (int_of_num (Nat.div x0 y0)) = (div (int_of_num x0) (int_of_num y0)).
Definition term5 (x0 : nat) := forall y0 : nat, (int_of_num (Nat.mul x0 y0)) = (int_mul (int_of_num x0) (int_of_num y0)).
Definition term52 := forall y0 : nat, True.
Definition term12 (x0 : nat) := fun y0 : nat => (div (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.div x0 y0)).
Definition term21 (x0 : int) := forall y0 : int, forall y1 : int, (int_divides y0 x0) -> (int_divides y1 (div x0 y0)) = (int_divides (int_mul y0 y1) x0).
Definition term41 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (int_divides (int_of_num x0) (div (int_of_num x1) (int_of_num x2))).
Definition term50 := fun y0 : nat => True.
Definition term44 (x0 : nat) (x1 : nat) := int_divides (int_of_num (Nat.mul x0 x1)).
Definition term14 (x0 : nat) := forall y0 : nat, (div (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.div x0 y0)).
Definition term4 (x0 : nat) := forall y0 : nat, (int_mul (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.mul x0 y0)).
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (num_divides x0 (Nat.div x1 x2)).
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) := int_divides (int_of_num x0) (int_of_num (Nat.div x1 x2)).
Definition term33 (x0 : nat) (x1 : nat) := (fun y0 : nat => (int_of_num (Nat.div x0 y0)) = (div (int_of_num x0) (int_of_num y0))) x1.
Definition term32 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (int_of_num (Nat.div y0 y1)) = (div (int_of_num y0) (int_of_num y1))) x0.
Definition term28 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (num_divides y0 y1) = (int_divides (int_of_num y0) (int_of_num y1))) x0.
Definition term26 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (int_of_num (Nat.mul y0 y1)) = (int_mul (int_of_num y0) (int_of_num y1))) x0.
Definition term45 (x0 : nat) (x1 : nat) := int_divides (int_mul (int_of_num x0) (int_of_num x1)).
Definition term30 (x0 : nat) (x1 : nat) := (fun y0 : nat => (num_divides x0 y0) = (int_divides (int_of_num x0) (int_of_num y0))) x1.
Definition term2 (x0 : nat) := fun y0 : nat => (int_mul (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.mul x0 y0)).
Definition term29 (x0 : nat) := forall y0 : nat, (num_divides x0 y0) = (int_divides (int_of_num x0) (int_of_num y0)).
Definition term54 (x0 : Prop) := forall y0 : nat, x0.
Definition term16 := fun y0 : nat => forall y1 : nat, (div (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.div y0 y1)).
Definition term6 := fun y0 : nat => forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1)).
Definition term46 (x0 : nat) (x1 : nat) (x2 : nat) := int_divides (int_mul (int_of_num x0) (int_of_num x1)) (int_of_num x2).
Definition term43 (x0 : nat) (x1 : nat) (x2 : nat) := int_divides (int_of_num (Nat.mul x0 x1)) (int_of_num x2).
Definition term0 (x0 : nat) (x1 : nat) := int_mul (int_of_num x0) (int_of_num x1).
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat) := (int_divides (int_of_num x0) (int_of_num x2)) -> (int_divides (int_of_num x1) (div (int_of_num x2) (int_of_num x0))) = (int_divides (int_mul (int_of_num x0) (int_of_num x1)) (int_of_num x2)).
Definition term55 (x0 : nat) := fun y0 : nat => forall y1 : nat, (num_divides y0 x0) -> (num_divides y1 (Nat.div x0 y0)) = (num_divides (Nat.mul y0 y1) x0).
Definition term17 := fun y0 : nat => forall y1 : nat, (int_of_num (Nat.div y0 y1)) = (div (int_of_num y0) (int_of_num y1)).
Definition term7 := fun y0 : nat => forall y1 : nat, (int_of_num (Nat.mul y0 y1)) = (int_mul (int_of_num y0) (int_of_num y1)).
Definition term57 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (num_divides y1 y0) -> (num_divides y2 (Nat.div y0 y1)) = (num_divides (Nat.mul y1 y2) y0).
Definition term31 (x0 : nat) (x1 : nat) := int_divides (int_of_num x0) (int_of_num x1).
