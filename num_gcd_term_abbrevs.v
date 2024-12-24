Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term21 (x0 : nat) := @eq (nat -> nat) ((fun y0 : nat => fun y1 : nat => num_of_int (int_gcd (@pair int int (int_of_num y0) (int_of_num y1)))) x0).
Definition term14 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @fst a0 a1 (@pair a0 a1 x0 x1).
Definition term26 (x0 : nat) (x1 : nat) := @eq nat ((fun y0 : nat => num_of_int (int_gcd (@pair int int (int_of_num x0) (int_of_num y0)))) x1).
Definition term5 (x0 : nat) (x1 : nat) := num_gcd (@pair nat nat x0 x1).
Definition term1 (x0 : prod nat nat) := (fun y0 : prod nat nat => num_of_int (int_gcd (@pair int int (int_of_num (@fst nat nat y0)) (int_of_num (@snd nat nat y0))))) x0.
Definition term2 (x0 : prod nat nat) := num_of_int (int_gcd (@pair int int (int_of_num (@fst nat nat x0)) (int_of_num (@snd nat nat x0)))).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a1, (@snd a0 a1 (@pair a0 a1 y0 y1)) = y1) x0.
Definition term12 (a0 : Type') (a1 : Type') (x0 : a0) := forall y0 : a1, (@fst a0 a1 (@pair a0 a1 x0 y0)) = x0.
Definition term16 (x0 : nat) (x1 : nat) := @snd nat nat (@pair nat nat x0 x1).
Definition term18 (x0 : nat) := (fun y0 : nat => fun y1 : nat => num_of_int (int_gcd (@pair int int (int_of_num y0) (int_of_num y1)))) x0.
Definition term24 (x0 : nat) (x1 : nat) := (fun y0 : nat => num_of_int (int_gcd (@pair int int (int_of_num x0) (int_of_num y0)))) x1.
Definition term19 (x0 : nat) (x1 : nat) := (fun y0 : nat => fun y1 : nat => num_of_int (int_gcd (@pair int int (int_of_num y0) (int_of_num y1)))) (@fst nat nat (@pair nat nat x0 x1)).
Definition term11 (a0 : Type') (a1 : Type') (x0 : a0) := (fun y0 : a0 => forall y1 : a1, (@fst a0 a1 (@pair a0 a1 y0 y1)) = y0) x0.
Definition term4 (x0 : prod nat nat) := (fun y0 : prod nat nat => (num_gcd y0) = (num_of_int (int_gcd (@pair int int (int_of_num (@fst nat nat y0)) (int_of_num (@snd nat nat y0)))))) x0.
Definition term29 (x0 : nat) := forall y0 : nat, (num_gcd (@pair nat nat x0 y0)) = (num_of_int (int_gcd (@pair int int (int_of_num x0) (int_of_num y0)))).
Definition term6 (x0 : nat) (x1 : nat) := num_of_int (int_gcd (@pair int int (int_of_num (@fst nat nat (@pair nat nat x0 x1))) (int_of_num (@snd nat nat (@pair nat nat x0 x1))))).
Definition term23 (x0 : nat) := @eq (nat -> nat) (fun y0 : nat => num_of_int (int_gcd (@pair int int (int_of_num x0) (int_of_num y0)))).
Definition term22 (x0 : nat) := fun y0 : nat => num_of_int (int_gcd (@pair int int (int_of_num x0) (int_of_num y0))).
Definition term20 (x0 : nat) (x1 : nat) := fun y0 : nat => num_of_int (int_gcd (@pair int int (int_of_num (@fst nat nat (@pair nat nat x0 x1))) (int_of_num y0))).
Definition term30 := forall y0 : nat, forall y1 : nat, (num_gcd (@pair nat nat y0 y1)) = (num_of_int (int_gcd (@pair int int (int_of_num y0) (int_of_num y1)))).
Definition term25 (x0 : nat) (x1 : nat) := (fun y0 : nat => num_of_int (int_gcd (@pair int int (int_of_num (@fst nat nat (@pair nat nat x0 x1))) (int_of_num y0)))) (@snd nat nat (@pair nat nat x0 x1)).
Definition term28 (x0 : nat) (x1 : nat) := @eq nat (num_of_int (int_gcd (@pair int int (int_of_num x0) (int_of_num x1)))).
Definition term3 := forall y0 : prod nat nat, (num_gcd y0) = (num_of_int (int_gcd (@pair int int (int_of_num (@fst nat nat y0)) (int_of_num (@snd nat nat y0))))).
Definition term15 (x0 : nat) (x1 : nat) := @fst nat nat (@pair nat nat x0 x1).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0) := forall y0 : a1, (@snd a0 a1 (@pair a0 a1 x0 y0)) = y0.
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (fun y0 : a1 => (@snd a0 a1 (@pair a0 a1 x0 y0)) = y0) x1.
Definition term10 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := @snd a0 a1 (@pair a0 a1 x0 x1).
Definition term13 (a0 : Type') (a1 : Type') (x0 : a0) (x1 : a1) := (fun y0 : a1 => (@fst a0 a1 (@pair a0 a1 x0 y0)) = x0) x1.
Definition term17 := fun y0 : nat => fun y1 : nat => num_of_int (int_gcd (@pair int int (int_of_num y0) (int_of_num y1))).
Definition term0 := fun y0 : prod nat nat => num_of_int (int_gcd (@pair int int (int_of_num (@fst nat nat y0)) (int_of_num (@snd nat nat y0)))).
Definition term27 (x0 : nat) (x1 : nat) := num_of_int (int_gcd (@pair int int (int_of_num x0) (int_of_num x1))).
