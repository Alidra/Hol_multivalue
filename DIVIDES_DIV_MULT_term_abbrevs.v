Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term10 (x0 : nat) (x1 : nat) := int_of_num (Nat.div x0 x1).
Definition term22 (x0 : nat) := fun y0 : nat => (int_of_num (Nat.mul x0 y0)) = (int_mul (int_of_num x0) (int_of_num y0)).
Definition term63 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term40 (x0 : int) := (fun y0 : int => forall y1 : int, ((int_mul (div y0 y1) y1) = y0) = (int_divides y1 y0)) x0.
Definition term31 (x0 : nat) := forall y0 : nat, ((int_of_num x0) = (int_of_num y0)) = (x0 = y0).
Definition term4 (x0 : nat) := forall y0 : nat, (int_divides (int_of_num x0) (int_of_num y0)) = (num_divides x0 y0).
Definition term57 (x0 : nat) (x1 : nat) := @eq int (int_mul (div (int_of_num x0) (int_of_num x1)) (int_of_num x1)).
Definition term58 (x0 : nat) (x1 : nat) := @eq Prop (num_divides x0 x1).
Definition term52 (x0 : nat) (x1 : nat) := int_mul (int_of_num (Nat.div x0 x1)) (int_of_num x1).
Definition term29 (x0 : nat) := fun y0 : nat => ((int_of_num x0) = (int_of_num y0)) = (x0 = y0).
Definition term49 (x0 : nat) (x1 : nat) := (fun y0 : nat => (x0 = y0) = ((int_of_num x0) = (int_of_num y0))) x1.
Definition term47 (x0 : nat) (x1 : nat) := (fun y0 : nat => (int_of_num (Nat.mul x0 y0)) = (int_mul (int_of_num x0) (int_of_num y0))) x1.
Definition term51 (x0 : nat) (x1 : nat) := int_of_num (Nat.mul (Nat.div x0 x1) x1).
Definition term59 (x0 : nat) := fun y0 : nat => (num_divides x0 y0) = ((Nat.mul (Nat.div y0 x0) x0) = y0).
Definition term65 := fun y0 : nat => forall y1 : nat, (num_divides y0 y1) = ((Nat.mul (Nat.div y1 y0) y0) = y1).
Definition term33 := fun y0 : nat => forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1).
Definition term6 := fun y0 : nat => forall y1 : nat, (int_divides (int_of_num y0) (int_of_num y1)) = (num_divides y0 y1).
Definition term50 (x0 : nat) (x1 : nat) := Nat.mul (Nat.div x0 x1) x1.
Definition term12 (x0 : nat) := fun y0 : nat => (int_of_num (Nat.div x0 y0)) = (div (int_of_num x0) (int_of_num y0)).
Definition term54 (x0 : nat) (x1 : nat) := int_mul (div (int_of_num x0) (int_of_num x1)).
Definition term9 (x0 : nat) (x1 : nat) := div (int_of_num x0) (int_of_num x1).
Definition term1 (x0 : nat) := fun y0 : nat => (num_divides x0 y0) = (int_divides (int_of_num x0) (int_of_num y0)).
Definition term56 (x0 : nat) (x1 : nat) := @eq int (int_of_num (Nat.mul (Nat.div x0 x1) x1)).
Definition term55 (x0 : nat) (x1 : nat) := int_mul (div (int_of_num x0) (int_of_num x1)) (int_of_num x1).
Definition term41 (x0 : int) := forall y0 : int, ((int_mul (div x0 y0) y0) = x0) = (int_divides y0 x0).
Definition term20 (x0 : nat) (x1 : nat) := int_of_num (Nat.mul x0 x1).
Definition term38 (x0 : nat) (x1 : nat) := (fun y0 : nat => (int_divides (int_of_num x0) (int_of_num y0)) = (num_divides x0 y0)) x1.
Definition term66 := forall y0 : nat, forall y1 : nat, (num_divides y0 y1) = ((Nat.mul (Nat.div y1 y0) y0) = y1).
Definition term36 := forall y0 : nat, forall y1 : nat, (y0 = y1) = ((int_of_num y0) = (int_of_num y1)).
Definition term35 := forall y0 : nat, forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1).
Definition term28 := forall y0 : nat, forall y1 : nat, (int_of_num (Nat.mul y0 y1)) = (int_mul (int_of_num y0) (int_of_num y1)).
Definition term27 := forall y0 : nat, forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1)).
Definition term18 := forall y0 : nat, forall y1 : nat, (int_of_num (Nat.div y0 y1)) = (div (int_of_num y0) (int_of_num y1)).
Definition term17 := forall y0 : nat, forall y1 : nat, (div (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.div y0 y1)).
Definition term8 := forall y0 : nat, forall y1 : nat, (int_divides (int_of_num y0) (int_of_num y1)) = (num_divides y0 y1).
Definition term7 := forall y0 : nat, forall y1 : nat, (num_divides y0 y1) = (int_divides (int_of_num y0) (int_of_num y1)).
Definition term24 (x0 : nat) := forall y0 : nat, (int_of_num (Nat.mul x0 y0)) = (int_mul (int_of_num x0) (int_of_num y0)).
Definition term14 (x0 : nat) := forall y0 : nat, (int_of_num (Nat.div x0 y0)) = (div (int_of_num x0) (int_of_num y0)).
Definition term62 := forall y0 : nat, True.
Definition term11 (x0 : nat) := fun y0 : nat => (div (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.div x0 y0)).
Definition term39 := forall y0 : int, forall y1 : int, ((int_mul (div y0 y1) y1) = y0) = (int_divides y1 y0).
Definition term61 (x0 : nat) := forall y0 : nat, (num_divides x0 y0) = ((Nat.mul (Nat.div y0 x0) x0) = y0).
Definition term60 := fun y0 : nat => True.
Definition term23 (x0 : nat) := forall y0 : nat, (int_mul (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.mul x0 y0)).
Definition term13 (x0 : nat) := forall y0 : nat, (div (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.div x0 y0)).
Definition term43 (x0 : int) (x1 : int) := int_mul (div x0 x1) x1.
Definition term2 (x0 : nat) := fun y0 : nat => (int_divides (int_of_num x0) (int_of_num y0)) = (num_divides x0 y0).
Definition term45 (x0 : nat) (x1 : nat) := (fun y0 : nat => (int_of_num (Nat.div x0 y0)) = (div (int_of_num x0) (int_of_num y0))) x1.
Definition term48 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (y0 = y1) = ((int_of_num y0) = (int_of_num y1))) x0.
Definition term46 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (int_of_num (Nat.mul y0 y1)) = (int_mul (int_of_num y0) (int_of_num y1))) x0.
Definition term44 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (int_of_num (Nat.div y0 y1)) = (div (int_of_num y0) (int_of_num y1))) x0.
Definition term37 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (int_divides (int_of_num y0) (int_of_num y1)) = (num_divides y0 y1)) x0.
Definition term30 (x0 : nat) := fun y0 : nat => (x0 = y0) = ((int_of_num x0) = (int_of_num y0)).
Definition term42 (x0 : int) (x1 : int) := (fun y0 : int => ((int_mul (div x0 y0) y0) = x0) = (int_divides y0 x0)) x1.
Definition term21 (x0 : nat) := fun y0 : nat => (int_mul (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.mul x0 y0)).
Definition term32 (x0 : nat) := forall y0 : nat, (x0 = y0) = ((int_of_num x0) = (int_of_num y0)).
Definition term3 (x0 : nat) := forall y0 : nat, (num_divides x0 y0) = (int_divides (int_of_num x0) (int_of_num y0)).
Definition term64 (x0 : Prop) := forall y0 : nat, x0.
Definition term25 := fun y0 : nat => forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1)).
Definition term15 := fun y0 : nat => forall y1 : nat, (div (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.div y0 y1)).
Definition term53 (x0 : nat) (x1 : nat) := int_mul (int_of_num (Nat.div x0 x1)).
Definition term19 (x0 : nat) (x1 : nat) := int_mul (int_of_num x0) (int_of_num x1).
Definition term34 := fun y0 : nat => forall y1 : nat, (y0 = y1) = ((int_of_num y0) = (int_of_num y1)).
Definition term26 := fun y0 : nat => forall y1 : nat, (int_of_num (Nat.mul y0 y1)) = (int_mul (int_of_num y0) (int_of_num y1)).
Definition term16 := fun y0 : nat => forall y1 : nat, (int_of_num (Nat.div y0 y1)) = (div (int_of_num y0) (int_of_num y1)).
Definition term5 := fun y0 : nat => forall y1 : nat, (num_divides y0 y1) = (int_divides (int_of_num y0) (int_of_num y1)).
Definition term0 (x0 : nat) (x1 : nat) := int_divides (int_of_num x0) (int_of_num x1).
