Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : nat) := @HAS_SIZE nat (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 x0) y1)) x0.
Definition term19 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term14 (x0 : nat) := @eq nat (@CARD nat (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 x0) y1))).
Definition term13 (x0 : nat) := @CARD nat (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 x0) y1)).
Definition term9 := fun y0 : nat => (@FINITE nat (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.lt y2 y0) y2))) /\ ((@CARD nat (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.lt y2 y0) y2))) = y0).
Definition term8 := fun y0 : nat => @HAS_SIZE nat (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.lt y2 y0) y2)) y0.
Definition term2 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (fun y0 : nat => (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0))) x1.
Definition term12 (x0 : nat) := (fun y0 : nat => (@FINITE nat (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.lt y2 y0) y2))) /\ ((@CARD nat (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.lt y2 y0) y2))) = y0)) x0.
Definition term18 := forall y0 : nat, True.
Definition term0 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => forall y1 : nat, (@HAS_SIZE a0 y0 y1) = ((@FINITE a0 y0) /\ ((@CARD a0 y0) = y1))) x0.
Definition term16 := fun y0 : nat => True.
Definition term4 (x0 : nat -> Prop) (x1 : nat) := (@FINITE nat x0) /\ ((@CARD nat x0) = x1).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) (x1 : nat) := (@FINITE a0 x0) /\ ((@CARD a0 x0) = x1).
Definition term17 := forall y0 : nat, (@CARD nat (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.lt y2 y0) y2))) = y0.
Definition term11 := forall y0 : nat, (@FINITE nat (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.lt y2 y0) y2))) /\ ((@CARD nat (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.lt y2 y0) y2))) = y0).
Definition term1 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : nat, (@HAS_SIZE a0 x0 y0) = ((@FINITE a0 x0) /\ ((@CARD a0 x0) = y0)).
Definition term15 := fun y0 : nat => (@CARD nat (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.lt y2 y0) y2))) = y0.
Definition term10 := forall y0 : nat, @HAS_SIZE nat (@GSPEC nat (fun y1 : nat => exists y2 : nat, @SETSPEC nat y1 (Peano.lt y2 y0) y2)) y0.
Definition term20 (x0 : Prop) := forall y0 : nat, x0.
Definition term6 (x0 : nat) := (@FINITE nat (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 x0) y1))) /\ ((@CARD nat (@GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 x0) y1))) = x0).
Definition term7 (x0 : nat) := @GSPEC nat (fun y0 : nat => exists y1 : nat, @SETSPEC nat y0 (Peano.lt y1 x0) y1).