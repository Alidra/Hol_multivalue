Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term28 := fun y0 : nat -> nat => True.
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := @sum nat (dotdot x0 x1) (fun y0 : nat => real_of_num (x2 y0)).
Definition term23 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term27 := fun y0 : nat -> nat => forall y1 : nat, forall y2 : nat, (real_of_num (@nsum nat (dotdot y1 y2) y0)) = (@sum nat (dotdot y1 y2) (fun y3 : nat => real_of_num (y0 y3))).
Definition term25 (x0 : nat -> nat) := fun y0 : nat => forall y1 : nat, (real_of_num (@nsum nat (dotdot y0 y1) x0)) = (@sum nat (dotdot y0 y1) (fun y2 : nat => real_of_num (x0 y2))).
Definition term5 (a0 : Type') (x0 : a0 -> nat) := forall y0 : a0 -> Prop, (@FINITE a0 y0) -> (real_of_num (@nsum a0 y0 x0)) = (@sum a0 y0 (fun y1 : a0 => real_of_num (x0 y1))).
Definition term29 := forall y0 : nat -> nat, forall y1 : nat, forall y2 : nat, (real_of_num (@nsum nat (dotdot y1 y2) y0)) = (@sum nat (dotdot y1 y2) (fun y3 : nat => real_of_num (y0 y3))).
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := @eq Prop ((fun y0 : Prop => y0 = True) ((@sum nat (dotdot x0 x1) (fun y0 : nat => real_of_num (x2 y0))) = (@sum nat (dotdot x0 x1) (fun y0 : nat => real_of_num (x2 y0))))).
Definition term1 (x0 : nat) := forall y0 : nat, @FINITE nat (dotdot x0 y0).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => @FINITE nat (dotdot x0 y0)) x1.
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := (fun y0 : Prop => y0 = True) ((@sum nat (dotdot x0 x1) (fun y0 : nat => real_of_num (x2 y0))) = (@sum nat (dotdot x0 x1) (fun y0 : nat => real_of_num (x2 y0)))).
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := @eq Prop (((@sum nat (dotdot x0 x1) (fun y0 : nat => real_of_num (x2 y0))) = (@sum nat (dotdot x0 x1) (fun y0 : nat => real_of_num (x2 y0)))) = True).
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := real_of_num (@nsum nat (dotdot x0 x1) x2).
Definition term30 := forall y0 : nat -> nat, True.
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := @eq real (real_of_num (@nsum nat (dotdot x0 x1) x2)).
Definition term26 (x0 : nat -> nat) := forall y0 : nat, forall y1 : nat, (real_of_num (@nsum nat (dotdot y0 y1) x0)) = (@sum nat (dotdot y0 y1) (fun y2 : nat => real_of_num (x0 y2))).
Definition term8 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := real_of_num (@nsum a0 x0 x1).
Definition term22 := forall y0 : nat, True.
Definition term10 (x0 : nat -> Prop) (x1 : nat -> nat) := (@FINITE nat x0) -> (real_of_num (@nsum nat x0 x1)) = (@sum nat x0 (fun y0 : nat => real_of_num (x1 y0))).
Definition term7 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := (@FINITE a0 x0) -> (real_of_num (@nsum a0 x0 x1)) = (@sum a0 x0 (fun y0 : a0 => real_of_num (x1 y0))).
Definition term4 (a0 : Type') (x0 : a0 -> nat) := (fun y0 : a0 -> nat => forall y1 : a0 -> Prop, (@FINITE a0 y1) -> (real_of_num (@nsum a0 y1 y0)) = (@sum a0 y1 (fun y2 : a0 => real_of_num (y0 y2)))) x0.
Definition term20 := fun y0 : nat => True.
Definition term6 (a0 : Type') (x0 : a0 -> nat) (x1 : a0 -> Prop) := (fun y0 : a0 -> Prop => (@FINITE a0 y0) -> (real_of_num (@nsum a0 y0 x0)) = (@sum a0 y0 (fun y1 : a0 => real_of_num (x0 y1)))) x1.
Definition term9 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> nat) := @sum a0 x0 (fun y0 : a0 => real_of_num (x1 y0)).
Definition term21 (x0 : nat) (x1 : nat -> nat) := forall y0 : nat, (real_of_num (@nsum nat (dotdot x0 y0) x1)) = (@sum nat (dotdot x0 y0) (fun y1 : nat => real_of_num (x1 y1))).
Definition term3 (x0 : nat) (x1 : nat) := @FINITE nat (dotdot x0 x1).
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := @eq real (@sum nat (dotdot x0 x1) (fun y0 : nat => real_of_num (x2 y0))).
Definition term31 (x0 : Prop) := forall y0 : nat -> nat, x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, @FINITE nat (dotdot y0 y1)) x0.
Definition term24 (x0 : Prop) := forall y0 : nat, x0.
Definition term19 (x0 : nat) (x1 : nat -> nat) := fun y0 : nat => (real_of_num (@nsum nat (dotdot x0 y0) x1)) = (@sum nat (dotdot x0 y0) (fun y1 : nat => real_of_num (x1 y1))).
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat -> nat) := (@FINITE nat (dotdot x0 x1)) -> (real_of_num (@nsum nat (dotdot x0 x1) x2)) = (@sum nat (dotdot x0 x1) (fun y0 : nat => real_of_num (x2 y0))).
