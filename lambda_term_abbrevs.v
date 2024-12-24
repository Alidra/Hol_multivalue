Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (a1 : Type') (x0 : nat -> a0) := (fun y0 : nat -> a0 => @ε (cart a0 a1) (fun y1 : cart a0 a1 => forall y2 : nat, ((Peano.le (NUMERAL (BIT1 0)) y2) /\ (Peano.le y2 (@dimindex a1 (@UNIV a1)))) -> (@dollar a0 a1 y1 y2) = (y0 y2))) x0.
Definition term3 (a0 : Type') (a1 : Type') := forall y0 : nat -> a0, (@lambda a0 a1 y0) = (@ε (cart a0 a1) (fun y1 : cart a0 a1 => forall y2 : nat, ((Peano.le (NUMERAL (BIT1 0)) y2) /\ (Peano.le y2 (@dimindex a1 (@UNIV a1)))) -> (@dollar a0 a1 y1 y2) = (y0 y2))).
Definition term2 (a0 : Type') (a1 : Type') (x0 : nat -> a0) := @ε (cart a0 a1) (fun y0 : cart a0 a1 => forall y1 : nat, ((Peano.le (NUMERAL (BIT1 0)) y1) /\ (Peano.le y1 (@dimindex a1 (@UNIV a1)))) -> (@dollar a0 a1 y0 y1) = (x0 y1)).
Definition term0 (a0 : Type') (a1 : Type') := fun y0 : nat -> a0 => @ε (cart a0 a1) (fun y1 : cart a0 a1 => forall y2 : nat, ((Peano.le (NUMERAL (BIT1 0)) y2) /\ (Peano.le y2 (@dimindex a1 (@UNIV a1)))) -> (@dollar a0 a1 y1 y2) = (y0 y2)).
Definition term4 (a0 : Type') (a1 : Type') (x0 : nat -> a0) := (fun y0 : nat -> a0 => (@lambda a0 a1 y0) = (@ε (cart a0 a1) (fun y1 : cart a0 a1 => forall y2 : nat, ((Peano.le (NUMERAL (BIT1 0)) y2) /\ (Peano.le y2 (@dimindex a1 (@UNIV a1)))) -> (@dollar a0 a1 y1 y2) = (y0 y2)))) x0.
