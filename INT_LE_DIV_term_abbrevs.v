Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term60 := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : nat, int_le (int_of_num (NUMERAL 0)) (div y0 (int_of_num y1)).
Definition term59 := fun y0 : int => forall y1 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le (int_of_num (NUMERAL 0)) y1)) -> int_le (int_of_num (NUMERAL 0)) (div y0 y1).
Definition term56 (x0 : int) := fun y0 : nat => int_le (int_of_num (NUMERAL 0)) (div x0 (int_of_num y0)).
Definition term20 (x0 : Prop) (x1 : Prop) (x2 : Prop) := x0 -> x1 -> x2.
Definition term44 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> int_le (int_of_num (NUMERAL 0)) (div x0 y0).
Definition term21 (x0 : int) (x1 : int) := ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le (int_of_num (NUMERAL 0)) x1)) -> int_le (int_of_num (NUMERAL 0)) (div x0 x1).
Definition term79 (x0 : nat) := fun y0 : nat => int_le (int_of_num (NUMERAL 0)) (div (int_of_num x0) (int_of_num y0)).
Definition term36 (x0 : int) := imp (int_le (int_of_num (NUMERAL 0)) x0).
Definition term24 (x0 : int) (x1 : int) := int_le (int_of_num (NUMERAL 0)) (div x0 x1).
Definition term6 (x0 : nat) (x1 : nat) := int_of_num (Nat.div x0 x1).
Definition term82 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term18 (x0 : int -> Prop) := (fun y0 : int -> Prop => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : nat, y0 (int_of_num y1))) x0.
Definition term22 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) x1) -> int_le (int_of_num (NUMERAL 0)) (div x0 x1).
Definition term66 (x0 : int) := (fun y0 : int => forall y1 : nat, int_le (int_of_num (NUMERAL 0)) (div y0 (int_of_num y1))) x0.
Definition term43 (x0 : int) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> int_le (int_of_num (NUMERAL 0)) (div x0 y0).
Definition term78 (x0 : nat) (x1 : nat) := int_le (int_of_num (NUMERAL 0)) (int_of_num (Nat.div x0 x1)).
Definition term27 (x0 : int) := forall y0 : int, ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le (int_of_num (NUMERAL 0)) y0)) -> int_le (int_of_num (NUMERAL 0)) (div x0 y0).
Definition term48 (x0 : int) (x1 : int) := (fun y0 : int => int_le (int_of_num (NUMERAL 0)) (div x0 y0)) x1.
Definition term15 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (forall y1 : a0, x0 -> y0 y1) = (x0 -> forall y1 : a0, y0 y1)) x1.
Definition term53 (x0 : int) (x1 : nat) := (fun y0 : int => int_le (int_of_num (NUMERAL 0)) (div x0 y0)) (int_of_num x1).
Definition term71 (x0 : nat) := (fun y0 : int => forall y1 : nat, int_le (int_of_num (NUMERAL 0)) (div y0 (int_of_num y1))) (int_of_num x0).
Definition term28 (x0 : int) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) y0) -> int_le (int_of_num (NUMERAL 0)) (div x0 y0).
Definition term57 (x0 : int) := forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (div x0 (int_of_num y0)).
Definition term77 (x0 : nat) (x1 : nat) := int_le (int_of_num (NUMERAL 0)) (div (int_of_num x0) (int_of_num x1)).
Definition term32 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> forall y0 : int, (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) -> int_le (int_of_num (NUMERAL 0)) (div x0 y1)) y0.
Definition term16 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := forall y0 : a0, x0 -> x1 y0.
Definition term13 (a0 : Type') (x0 : Prop) := (fun y0 : Prop => forall y1 : a0 -> Prop, (forall y2 : a0, y0 -> y1 y2) = (y0 -> forall y2 : a0, y1 y2)) x0.
Definition term55 (x0 : int) := fun y0 : nat => (fun y1 : int => int_le (int_of_num (NUMERAL 0)) (div x0 y1)) (int_of_num y0).
Definition term14 (a0 : Type') (x0 : Prop) := forall y0 : a0 -> Prop, (forall y1 : a0, x0 -> y0 y1) = (x0 -> forall y1 : a0, y0 y1).
Definition term0 (x0 : nat) := (fun y0 : nat => int_le (int_of_num (NUMERAL 0)) (int_of_num y0)) x0.
Definition term70 := @eq Prop (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : nat, int_le (int_of_num (NUMERAL 0)) (div y0 (int_of_num y1))).
Definition term69 := @eq Prop (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => forall y2 : nat, int_le (int_of_num (NUMERAL 0)) (div y1 (int_of_num y2))) y0).
Definition term52 (x0 : int) := @eq Prop (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> int_le (int_of_num (NUMERAL 0)) (div x0 y0)).
Definition term51 (x0 : int) := @eq Prop (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => int_le (int_of_num (NUMERAL 0)) (div x0 y1)) y0).
Definition term40 (x0 : int) := @eq Prop (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) y0) -> int_le (int_of_num (NUMERAL 0)) (div x0 y0)).
Definition term39 (x0 : int) := @eq Prop (forall y0 : int, (int_le (int_of_num (NUMERAL 0)) x0) -> (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) -> int_le (int_of_num (NUMERAL 0)) (div x0 y1)) y0).
Definition term5 (x0 : nat) (x1 : nat) := div (int_of_num x0) (int_of_num x1).
Definition term12 := forall y0 : int -> Prop, (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : nat, y0 (int_of_num y1)).
Definition term11 := forall y0 : int -> Prop, (forall y1 : nat, y0 (int_of_num y1)) = (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1).
Definition term17 (a0 : Type') (x0 : Prop) (x1 : a0 -> Prop) := x0 -> forall y0 : a0, x1 y0.
Definition term38 (x0 : int) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) x0) -> (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) -> int_le (int_of_num (NUMERAL 0)) (div x0 y1)) y0.
Definition term10 := fun y0 : int -> Prop => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : nat, y0 (int_of_num y1)).
Definition term9 := fun y0 : int -> Prop => (forall y1 : nat, y0 (int_of_num y1)) = (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1).
Definition term75 := forall y0 : nat, forall y1 : nat, int_le (int_of_num (NUMERAL 0)) (div (int_of_num y0) (int_of_num y1)).
Definition term34 (x0 : int) (x1 : int) := (fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> int_le (int_of_num (NUMERAL 0)) (div x0 y0)) x1.
Definition term49 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> (fun y0 : int => int_le (int_of_num (NUMERAL 0)) (div x0 y0)) x1.
Definition term50 (x0 : int) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => int_le (int_of_num (NUMERAL 0)) (div x0 y1)) y0.
Definition term8 (x0 : int -> Prop) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> x0 y0.
Definition term81 := forall y0 : nat, True.
Definition term61 := forall y0 : int, forall y1 : int, ((int_le (int_of_num (NUMERAL 0)) y0) /\ (int_le (int_of_num (NUMERAL 0)) y1)) -> int_le (int_of_num (NUMERAL 0)) (div y0 y1).
Definition term25 (x0 : int) := fun y0 : int => ((int_le (int_of_num (NUMERAL 0)) x0) /\ (int_le (int_of_num (NUMERAL 0)) y0)) -> int_le (int_of_num (NUMERAL 0)) (div x0 y0).
Definition term80 := fun y0 : nat => True.
Definition term29 (x0 : Prop) (x1 : int -> Prop) := forall y0 : int, x0 -> x1 y0.
Definition term3 (x0 : nat) := forall y0 : nat, (div (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.div x0 y0)).
Definition term73 := fun y0 : nat => (fun y1 : int => forall y2 : nat, int_le (int_of_num (NUMERAL 0)) (div y1 (int_of_num y2))) (int_of_num y0).
Definition term26 (x0 : int) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) x0) -> (int_le (int_of_num (NUMERAL 0)) y0) -> int_le (int_of_num (NUMERAL 0)) (div x0 y0).
Definition term19 (x0 : Prop) (x1 : Prop) (x2 : Prop) := (x0 /\ x1) -> x2.
Definition term68 := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => forall y2 : nat, int_le (int_of_num (NUMERAL 0)) (div y1 (int_of_num y2))) y0.
Definition term1 (x0 : nat) := int_le (int_of_num (NUMERAL 0)) (int_of_num x0).
Definition term2 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (div (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.div y0 y1))) x0.
Definition term4 (x0 : nat) (x1 : nat) := (fun y0 : nat => (div (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.div x0 y0))) x1.
Definition term67 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> (fun y0 : int => forall y1 : nat, int_le (int_of_num (NUMERAL 0)) (div y0 (int_of_num y1))) x0.
Definition term7 (x0 : int -> Prop) := forall y0 : nat, x0 (int_of_num y0).
Definition term72 (x0 : nat) := forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (div (int_of_num x0) (int_of_num y0)).
Definition term46 (x0 : int) := forall y0 : nat, (fun y1 : int => int_le (int_of_num (NUMERAL 0)) (div x0 y1)) (int_of_num y0).
Definition term62 := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> forall y1 : nat, int_le (int_of_num (NUMERAL 0)) (div y0 (int_of_num y1)).
Definition term63 := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => forall y2 : nat, int_le (int_of_num (NUMERAL 0)) (div y1 (int_of_num y2))) y0.
Definition term45 (x0 : int) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> (fun y1 : int => int_le (int_of_num (NUMERAL 0)) (div x0 y1)) y0.
Definition term31 (x0 : int) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) x0) -> (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) -> int_le (int_of_num (NUMERAL 0)) (div x0 y1)) y0.
Definition term30 (x0 : Prop) (x1 : int -> Prop) := x0 -> forall y0 : int, x1 y0.
Definition term83 (x0 : Prop) := forall y0 : nat, x0.
Definition term23 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term64 := forall y0 : nat, (fun y1 : int => forall y2 : nat, int_le (int_of_num (NUMERAL 0)) (div y1 (int_of_num y2))) (int_of_num y0).
Definition term37 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> (fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> int_le (int_of_num (NUMERAL 0)) (div x0 y0)) x1.
Definition term76 := int_le (int_of_num (NUMERAL 0)).
Definition term41 (x0 : int) := fun y0 : int => (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) -> int_le (int_of_num (NUMERAL 0)) (div x0 y1)) y0.
Definition term65 := fun y0 : int => forall y1 : nat, int_le (int_of_num (NUMERAL 0)) (div y0 (int_of_num y1)).
Definition term58 (x0 : int) := (int_le (int_of_num (NUMERAL 0)) x0) -> forall y0 : nat, int_le (int_of_num (NUMERAL 0)) (div x0 (int_of_num y0)).
Definition term35 (x0 : int) (x1 : int) := (int_le (int_of_num (NUMERAL 0)) x1) -> int_le (int_of_num (NUMERAL 0)) (div x0 x1).
Definition term42 (x0 : int) := forall y0 : int, (fun y1 : int => (int_le (int_of_num (NUMERAL 0)) y1) -> int_le (int_of_num (NUMERAL 0)) (div x0 y1)) y0.
Definition term54 (x0 : int) (x1 : nat) := int_le (int_of_num (NUMERAL 0)) (div x0 (int_of_num x1)).
Definition term74 := fun y0 : nat => forall y1 : nat, int_le (int_of_num (NUMERAL 0)) (div (int_of_num y0) (int_of_num y1)).
Definition term33 (x0 : int) := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) -> int_le (int_of_num (NUMERAL 0)) (div x0 y0).
Definition term47 (x0 : int) := fun y0 : int => int_le (int_of_num (NUMERAL 0)) (div x0 y0).
