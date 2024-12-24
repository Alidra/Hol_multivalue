Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) (x5 : Prop) := ((@eq2 nat x0 x1 (num_mod (Nat.mul x2 x3))) = x4) -> (x4 -> (@eq2 nat (Nat.div x0 x2) (Nat.div x1 x2) (num_mod x3)) = x5) -> ((@eq2 nat x0 x1 (num_mod (Nat.mul x2 x3))) -> @eq2 nat (Nat.div x0 x2) (Nat.div x1 x2) (num_mod x3)) = (x4 -> x5).
Definition term7 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (@eq2 nat y0 y1 (num_mod y2)) = ((Nat.modulo y0 y2) = (Nat.modulo y1 y2))) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.div y0 y1) y2) = (Nat.div (Nat.modulo y0 (Nat.mul y1 y2)) y1)) x0.
Definition term37 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo x0 (Nat.mul x1 x2).
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (@eq2 nat x0 x1 (num_mod y0)) = ((Nat.modulo x0 y0) = (Nat.modulo x1 y0))) x2.
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq2 nat x0 x1 (num_mod (Nat.mul x2 x3)).
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.div (Nat.modulo x0 (Nat.mul x2 x1)) x2).
Definition term32 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.modulo x0 (Nat.mul x2 x3)) = (Nat.modulo x1 (Nat.mul x2 x3))) -> True.
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (@eq2 nat x0 x1 (num_mod (Nat.mul x2 y0))) -> @eq2 nat (Nat.div x0 x2) (Nat.div x1 x2) (num_mod y0).
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := @eq2 nat (Nat.div x0 x2) (Nat.div x1 x2) (num_mod x3).
Definition term9 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (@eq2 nat x0 y0 (num_mod y1)) = ((Nat.modulo x0 y1) = (Nat.modulo y0 y1))) x1.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.modulo (Nat.div x0 y0) y1) = (Nat.div (Nat.modulo x0 (Nat.mul y0 y1)) y0)) x1.
Definition term13 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.modulo (Nat.div x0 x1) x2.
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (((Nat.modulo x0 (Nat.mul x2 x3)) = (Nat.modulo x1 (Nat.mul x2 x3))) -> (@eq2 nat (Nat.div x0 x2) (Nat.div x1 x2) (num_mod x3)) = True) -> ((@eq2 nat x0 x1 (num_mod (Nat.mul x2 x3))) -> @eq2 nat (Nat.div x0 x2) (Nat.div x1 x2) (num_mod x3)) = (((Nat.modulo x0 (Nat.mul x2 x3)) = (Nat.modulo x1 (Nat.mul x2 x3))) -> True).
Definition term44 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, (@eq2 nat y0 y1 (num_mod (Nat.mul y2 y3))) -> @eq2 nat (Nat.div y0 y2) (Nat.div y1 y2) (num_mod y3).
Definition term42 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, (@eq2 nat x0 y0 (num_mod (Nat.mul y1 y2))) -> @eq2 nat (Nat.div x0 y1) (Nat.div y0 y1) (num_mod y2).
Definition term40 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, (@eq2 nat x0 x1 (num_mod (Nat.mul y0 y1))) -> @eq2 nat (Nat.div x0 y0) (Nat.div x1 y0) (num_mod y1).
Definition term8 (x0 : nat) := forall y0 : nat, forall y1 : nat, (@eq2 nat x0 y0 (num_mod y1)) = ((Nat.modulo x0 y1) = (Nat.modulo y0 y1)).
Definition term1 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.modulo (Nat.div x0 y0) y1) = (Nat.div (Nat.modulo x0 (Nat.mul y0 y1)) y0).
Definition term31 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (@eq2 nat x0 x1 (num_mod (Nat.mul x2 x3))) -> @eq2 nat (Nat.div x0 x2) (Nat.div x1 x2) (num_mod x3).
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.div (Nat.modulo x0 (Nat.mul x1 x2)).
Definition term36 := forall y0 : nat, True.
Definition term34 := fun y0 : nat => True.
Definition term10 (x0 : nat) (x1 : nat) := forall y0 : nat, (@eq2 nat x0 x1 (num_mod y0)) = ((Nat.modulo x0 y0) = (Nat.modulo x1 y0)).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.div (Nat.modulo x0 (Nat.mul x2 x1)) x2.
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := (((Nat.modulo x0 (Nat.mul x2 x3)) = (Nat.modulo x1 (Nat.mul x2 x3))) -> (@eq2 nat (Nat.div x0 x2) (Nat.div x1 x2) (num_mod x3)) = x4) -> ((@eq2 nat x0 x1 (num_mod (Nat.mul x2 x3))) -> @eq2 nat (Nat.div x0 x2) (Nat.div x1 x2) (num_mod x3)) = (((Nat.modulo x0 (Nat.mul x2 x3)) = (Nat.modulo x1 (Nat.mul x2 x3))) -> x4).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Nat.modulo x0 (Nat.mul x2 x3)) = (Nat.modulo x1 (Nat.mul x2 x3))) -> (@eq2 nat (Nat.div x0 x2) (Nat.div x1 x2) (num_mod x3)) = True.
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := forall y0 : Prop, ((@eq2 nat x0 x1 (num_mod (Nat.mul x2 x3))) = x4) -> (x4 -> (@eq2 nat (Nat.div x0 x2) (Nat.div x1 x2) (num_mod x3)) = y0) -> ((@eq2 nat x0 x1 (num_mod (Nat.mul x2 x3))) -> @eq2 nat (Nat.div x0 x2) (Nat.div x1 x2) (num_mod x3)) = (x4 -> y0).
Definition term14 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.modulo (Nat.div x0 x1) y0) = (Nat.div (Nat.modulo x0 (Nat.mul x1 y0)) x1)) x2.
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := forall y0 : Prop, forall y1 : Prop, ((@eq2 nat x0 x1 (num_mod (Nat.mul x2 x3))) = y0) -> (y0 -> (@eq2 nat (Nat.div x0 x2) (Nat.div x1 x2) (num_mod x3)) = y1) -> ((@eq2 nat x0 x1 (num_mod (Nat.mul x2 x3))) -> @eq2 nat (Nat.div x0 x2) (Nat.div x1 x2) (num_mod x3)) = (y0 -> y1).
Definition term15 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) := @eq2 nat x0 x1 (num_mod x2).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := @eq nat (Nat.modulo (Nat.div x0 x1) x2).
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) (x5 : Prop) := (fun y0 : Prop => ((@eq2 nat x0 x1 (num_mod (Nat.mul x2 x3))) = x4) -> (x4 -> (@eq2 nat (Nat.div x0 x2) (Nat.div x1 x2) (num_mod x3)) = y0) -> ((@eq2 nat x0 x1 (num_mod (Nat.mul x2 x3))) -> @eq2 nat (Nat.div x0 x2) (Nat.div x1 x2) (num_mod x3)) = (x4 -> y0)) x5.
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := ((@eq2 nat x0 x1 (num_mod (Nat.mul x2 x3))) = ((Nat.modulo x0 (Nat.mul x2 x3)) = (Nat.modulo x1 (Nat.mul x2 x3)))) -> (((Nat.modulo x0 (Nat.mul x2 x3)) = (Nat.modulo x1 (Nat.mul x2 x3))) -> (@eq2 nat (Nat.div x0 x2) (Nat.div x1 x2) (num_mod x3)) = x4) -> ((@eq2 nat x0 x1 (num_mod (Nat.mul x2 x3))) -> @eq2 nat (Nat.div x0 x2) (Nat.div x1 x2) (num_mod x3)) = (((Nat.modulo x0 (Nat.mul x2 x3)) = (Nat.modulo x1 (Nat.mul x2 x3))) -> x4).
Definition term38 (x0 : Prop) := forall y0 : nat, x0.
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) (x4 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((@eq2 nat x0 x1 (num_mod (Nat.mul x2 x3))) = y0) -> (y0 -> (@eq2 nat (Nat.div x0 x2) (Nat.div x1 x2) (num_mod x3)) = y1) -> ((@eq2 nat x0 x1 (num_mod (Nat.mul x2 x3))) -> @eq2 nat (Nat.div x0 x2) (Nat.div x1 x2) (num_mod x3)) = (y0 -> y1)) x4.
Definition term3 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.modulo (Nat.div x0 x1) y0) = (Nat.div (Nat.modulo x0 (Nat.mul x1 y0)) x1).
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, (@eq2 nat x0 x1 (num_mod (Nat.mul x2 y0))) -> @eq2 nat (Nat.div x0 x2) (Nat.div x1 x2) (num_mod y0).
Definition term39 (x0 : nat) (x1 : nat) := fun y0 : nat => forall y1 : nat, (@eq2 nat x0 x1 (num_mod (Nat.mul y0 y1))) -> @eq2 nat (Nat.div x0 y0) (Nat.div x1 y0) (num_mod y1).
Definition term43 := fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, (@eq2 nat y0 y1 (num_mod (Nat.mul y2 y3))) -> @eq2 nat (Nat.div y0 y2) (Nat.div y1 y2) (num_mod y3).
Definition term41 (x0 : nat) := fun y0 : nat => forall y1 : nat, forall y2 : nat, (@eq2 nat x0 y0 (num_mod (Nat.mul y1 y2))) -> @eq2 nat (Nat.div x0 y1) (Nat.div y0 y1) (num_mod y2).
