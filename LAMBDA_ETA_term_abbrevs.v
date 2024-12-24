Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term14 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : nat) := ((Peano.le (NUMERAL (BIT1 0)) x1) /\ (Peano.le x1 (@dimindex a1 (@UNIV a1)))) -> (@dollar a0 a1 (@lambda a0 a1 (fun y0 : nat => @dollar a0 a1 x0 y0)) x1) = (@dollar a0 a1 x0 x1).
Definition term12 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : nat) := @dollar a0 a1 (@lambda a0 a1 (fun y0 : nat => @dollar a0 a1 x0 y0)) x1.
Definition term8 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : nat) := ((Peano.le (NUMERAL (BIT1 0)) x1) /\ (Peano.le x1 (@dimindex a1 (@UNIV a1)))) -> (@dollar a0 a1 (@lambda a0 a1 (fun y0 : nat => @dollar a0 a1 x0 y0)) x1) = ((fun y0 : nat => @dollar a0 a1 x0 y0) x1).
Definition term20 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term4 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := (fun y0 : cart a0 a1 => (x0 = y0) = (forall y1 : nat, ((Peano.le (NUMERAL (BIT1 0)) y1) /\ (Peano.le y1 (@dimindex a1 (@UNIV a1)))) -> (@dollar a0 a1 x0 y1) = (@dollar a0 a1 y0 y1))) x1.
Definition term23 (a0 : Type') (a1 : Type') := fun y0 : cart a0 a1 => True.
Definition term3 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := forall y0 : cart a0 a1, (x0 = y0) = (forall y1 : nat, ((Peano.le (NUMERAL (BIT1 0)) y1) /\ (Peano.le y1 (@dimindex a1 (@UNIV a1)))) -> (@dollar a0 a1 x0 y1) = (@dollar a0 a1 y0 y1)).
Definition term24 (a0 : Type') (a1 : Type') := forall y0 : cart a0 a1, (@lambda a0 a1 (fun y1 : nat => @dollar a0 a1 y0 y1)) = y0.
Definition term22 (a0 : Type') (a1 : Type') := fun y0 : cart a0 a1 => (@lambda a0 a1 (fun y1 : nat => @dollar a0 a1 y0 y1)) = y0.
Definition term15 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : nat) := @eq Prop (((Peano.le (NUMERAL (BIT1 0)) x1) /\ (Peano.le x1 (@dimindex a1 (@UNIV a1)))) -> (@dollar a0 a1 (@lambda a0 a1 (fun y0 : nat => @dollar a0 a1 x0 y0)) x1) = ((fun y0 : nat => @dollar a0 a1 x0 y0) x1)).
Definition term13 (a0 : Type') (x0 : nat) := imp ((Peano.le (NUMERAL (BIT1 0)) x0) /\ (Peano.le x0 (@dimindex a0 (@UNIV a0)))).
Definition term16 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : nat) := @eq Prop (((Peano.le (NUMERAL (BIT1 0)) x1) /\ (Peano.le x1 (@dimindex a1 (@UNIV a1)))) -> (@dollar a0 a1 (@lambda a0 a1 (fun y0 : nat => @dollar a0 a1 x0 y0)) x1) = (@dollar a0 a1 x0 x1)).
Definition term0 (a0 : Type') (a1 : Type') (x0 : nat -> a0) (x1 : nat) := (fun y0 : nat => ((Peano.le (NUMERAL (BIT1 0)) y0) /\ (Peano.le y0 (@dimindex a1 (@UNIV a1)))) -> (@dollar a0 a1 (@lambda a0 a1 x0) y0) = (x0 y0)) x1.
Definition term11 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : nat) := @eq a0 (@dollar a0 a1 (@lambda a0 a1 (fun y0 : nat => @dollar a0 a1 x0 y0)) x1).
Definition term26 (a0 : Type') (a1 : Type') (x0 : Prop) := forall y0 : cart a0 a1, x0.
Definition term10 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : nat) := (fun y0 : nat => @dollar a0 a1 x0 y0) x1.
Definition term19 := forall y0 : nat, True.
Definition term25 (a0 : Type') (a1 : Type') := forall y0 : cart a0 a1, True.
Definition term18 := fun y0 : nat => True.
Definition term1 (a0 : Type') (a1 : Type') (x0 : nat -> a0) (x1 : nat) := ((Peano.le (NUMERAL (BIT1 0)) x1) /\ (Peano.le x1 (@dimindex a1 (@UNIV a1)))) -> (@dollar a0 a1 (@lambda a0 a1 x0) x1) = (x0 x1).
Definition term2 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := (fun y0 : cart a0 a1 => forall y1 : cart a0 a1, (y0 = y1) = (forall y2 : nat, ((Peano.le (NUMERAL (BIT1 0)) y2) /\ (Peano.le y2 (@dimindex a1 (@UNIV a1)))) -> (@dollar a0 a1 y0 y2) = (@dollar a0 a1 y1 y2))) x0.
Definition term17 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := fun y0 : nat => ((Peano.le (NUMERAL (BIT1 0)) y0) /\ (Peano.le y0 (@dimindex a1 (@UNIV a1)))) -> (@dollar a0 a1 (@lambda a0 a1 (fun y1 : nat => @dollar a0 a1 x0 y1)) y0) = (@dollar a0 a1 x0 y0).
Definition term7 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := forall y0 : nat, ((Peano.le (NUMERAL (BIT1 0)) y0) /\ (Peano.le y0 (@dimindex a1 (@UNIV a1)))) -> (@dollar a0 a1 (@lambda a0 a1 (fun y1 : nat => @dollar a0 a1 x0 y1)) y0) = (@dollar a0 a1 x0 y0).
Definition term5 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) (x1 : cart a0 a1) := forall y0 : nat, ((Peano.le (NUMERAL (BIT1 0)) y0) /\ (Peano.le y0 (@dimindex a1 (@UNIV a1)))) -> (@dollar a0 a1 x0 y0) = (@dollar a0 a1 x1 y0).
Definition term9 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := fun y0 : nat => @dollar a0 a1 x0 y0.
Definition term6 (a0 : Type') (a1 : Type') (x0 : cart a0 a1) := @lambda a0 a1 (fun y0 : nat => @dollar a0 a1 x0 y0).
Definition term21 (x0 : Prop) := forall y0 : nat, x0.
