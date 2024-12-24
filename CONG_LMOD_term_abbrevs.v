Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (@eq2 nat y0 y1 (num_mod y2)) = ((Nat.modulo y0 y2) = (Nat.modulo y1 y2))) x0.
Definition term19 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (@eq2 nat x0 x1 (num_mod y0)) = ((Nat.modulo x0 y0) = (Nat.modulo x1 y0))) x2.
Definition term3 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.modulo x0 x1) x1.
Definition term12 (x0 : nat) (x1 : nat) := @eq nat (Nat.modulo x0 x1).
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (@eq2 nat (Nat.modulo x0 x2) x1 (num_mod x2)).
Definition term6 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (@eq2 nat x0 y0 (num_mod y1)) = ((Nat.modulo x0 y1) = (Nat.modulo y0 y1))) x1.
Definition term11 (x0 : nat) (x1 : nat) := @eq nat (Nat.modulo (Nat.modulo x0 x1) x1).
Definition term1 (x0 : nat) := forall y0 : nat, (Nat.modulo (Nat.modulo x0 y0) y0) = (Nat.modulo x0 y0).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.modulo (Nat.modulo x0 y0) y0) = (Nat.modulo x0 y0)) x1.
Definition term24 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (@eq2 nat (Nat.modulo y0 y2) y1 (num_mod y2)) = (@eq2 nat y0 y1 (num_mod y2)).
Definition term22 (x0 : nat) := forall y0 : nat, forall y1 : nat, (@eq2 nat (Nat.modulo x0 y1) y0 (num_mod y1)) = (@eq2 nat x0 y0 (num_mod y1)).
Definition term5 (x0 : nat) := forall y0 : nat, forall y1 : nat, (@eq2 nat x0 y0 (num_mod y1)) = ((Nat.modulo x0 y1) = (Nat.modulo y0 y1)).
Definition term18 := forall y0 : nat, True.
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) := @eq2 nat (Nat.modulo x0 x2) x1 (num_mod x2).
Definition term16 := fun y0 : nat => True.
Definition term7 (x0 : nat) (x1 : nat) := forall y0 : nat, (@eq2 nat x0 x1 (num_mod y0)) = ((Nat.modulo x0 y0) = (Nat.modulo x1 y0)).
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) := @eq2 nat x0 x1 (num_mod x2).
Definition term15 (x0 : nat) (x1 : nat) := fun y0 : nat => (@eq2 nat (Nat.modulo x0 y0) x1 (num_mod y0)) = (@eq2 nat x0 x1 (num_mod y0)).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.modulo (Nat.modulo y0 y1) y1) = (Nat.modulo y0 y1)) x0.
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Nat.modulo x0 x2) = (Nat.modulo x1 x2)).
Definition term17 (x0 : nat) (x1 : nat) := forall y0 : nat, (@eq2 nat (Nat.modulo x0 y0) x1 (num_mod y0)) = (@eq2 nat x0 x1 (num_mod y0)).
Definition term20 (x0 : Prop) := forall y0 : nat, x0.
Definition term21 (x0 : nat) := fun y0 : nat => forall y1 : nat, (@eq2 nat (Nat.modulo x0 y1) y0 (num_mod y1)) = (@eq2 nat x0 y0 (num_mod y1)).
Definition term23 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (@eq2 nat (Nat.modulo y0 y2) y1 (num_mod y2)) = (@eq2 nat y0 y1 (num_mod y2)).
