Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 (x0 : int) := forall y0 : int, (int_divides y0 x0) -> int_divides (div x0 y0) x0.
Definition term1 (x0 : nat) (x1 : nat) := int_of_num (Nat.div x0 x1).
Definition term33 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term10 (x0 : int) := (fun y0 : int => forall y1 : int, (int_divides y1 y0) -> int_divides (div y0 y1) y0) x0.
Definition term20 (x0 : nat) (x1 : nat) := imp (num_divides x0 x1).
Definition term21 (x0 : nat) (x1 : nat) := imp (int_divides (int_of_num x0) (int_of_num x1)).
Definition term12 (x0 : int) (x1 : int) := (fun y0 : int => (int_divides y0 x0) -> int_divides (div x0 y0) x0) x1.
Definition term25 (x0 : nat) (x1 : nat) := int_divides (div (int_of_num x0) (int_of_num x1)).
Definition term35 := fun y0 : nat => forall y1 : nat, (num_divides y1 y0) -> num_divides (Nat.div y0 y1) y0.
Definition term3 (x0 : nat) := fun y0 : nat => (int_of_num (Nat.div x0 y0)) = (div (int_of_num x0) (int_of_num y0)).
Definition term0 (x0 : nat) (x1 : nat) := div (int_of_num x0) (int_of_num x1).
Definition term22 (x0 : nat) (x1 : nat) := num_divides (Nat.div x1 x0) x1.
Definition term36 := forall y0 : nat, forall y1 : nat, (num_divides y1 y0) -> num_divides (Nat.div y0 y1) y0.
Definition term9 := forall y0 : nat, forall y1 : nat, (int_of_num (Nat.div y0 y1)) = (div (int_of_num y0) (int_of_num y1)).
Definition term8 := forall y0 : nat, forall y1 : nat, (div (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.div y0 y1)).
Definition term5 (x0 : nat) := forall y0 : nat, (int_of_num (Nat.div x0 y0)) = (div (int_of_num x0) (int_of_num y0)).
Definition term32 := forall y0 : nat, True.
Definition term2 (x0 : nat) := fun y0 : nat => (div (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.div x0 y0)).
Definition term30 := fun y0 : nat => True.
Definition term24 (x0 : nat) (x1 : nat) := int_divides (int_of_num (Nat.div x0 x1)).
Definition term4 (x0 : nat) := forall y0 : nat, (div (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.div x0 y0)).
Definition term27 (x0 : nat) (x1 : nat) := (num_divides x0 x1) -> num_divides (Nat.div x1 x0) x1.
Definition term13 (x0 : int) (x1 : int) := (int_divides x0 x1) -> int_divides (div x1 x0) x1.
Definition term26 (x0 : nat) (x1 : nat) := int_divides (div (int_of_num x1) (int_of_num x0)) (int_of_num x1).
Definition term15 (x0 : nat) (x1 : nat) := (fun y0 : nat => (int_of_num (Nat.div x0 y0)) = (div (int_of_num x0) (int_of_num y0))) x1.
Definition term16 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (num_divides y0 y1) = (int_divides (int_of_num y0) (int_of_num y1))) x0.
Definition term14 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (int_of_num (Nat.div y0 y1)) = (div (int_of_num y0) (int_of_num y1))) x0.
Definition term18 (x0 : nat) (x1 : nat) := (fun y0 : nat => (num_divides x0 y0) = (int_divides (int_of_num x0) (int_of_num y0))) x1.
Definition term29 (x0 : nat) := fun y0 : nat => (num_divides y0 x0) -> num_divides (Nat.div x0 y0) x0.
Definition term28 (x0 : nat) (x1 : nat) := (int_divides (int_of_num x0) (int_of_num x1)) -> int_divides (div (int_of_num x1) (int_of_num x0)) (int_of_num x1).
Definition term17 (x0 : nat) := forall y0 : nat, (num_divides x0 y0) = (int_divides (int_of_num x0) (int_of_num y0)).
Definition term34 (x0 : Prop) := forall y0 : nat, x0.
Definition term6 := fun y0 : nat => forall y1 : nat, (div (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.div y0 y1)).
Definition term7 := fun y0 : nat => forall y1 : nat, (int_of_num (Nat.div y0 y1)) = (div (int_of_num y0) (int_of_num y1)).
Definition term23 (x0 : nat) (x1 : nat) := int_divides (int_of_num (Nat.div x1 x0)) (int_of_num x1).
Definition term19 (x0 : nat) (x1 : nat) := int_divides (int_of_num x0) (int_of_num x1).
Definition term31 (x0 : nat) := forall y0 : nat, (num_divides y0 x0) -> num_divides (Nat.div x0 y0) x0.
