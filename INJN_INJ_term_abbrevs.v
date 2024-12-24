Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term14 (a0 : Type') (x0 : nat) := @eq (a0 -> Prop) ((fun y0 : nat => fun y1 : a0 => y0 = x0) x0).
Definition term19 (a0 : Type') (x0 : a0) := (fun y0 : a0 => (fun y1 : a0 => True) y0) x0.
Definition term29 (a0 : Type') (x0 : nat) (x1 : nat) := fun y0 : a0 => (fun y1 : a0 => x0 = x1) y0.
Definition term15 (a0 : Type') (x0 : nat) := fun y0 : a0 => x0 = x0.
Definition term26 (a0 : Type') (x0 : nat) (x1 : nat) := @eq (a0 -> Prop) ((fun y0 : nat => fun y1 : a0 => y0 = x0) x1).
Definition term35 (x0 : nat) (x1 : nat) := (x0 = x1) -> x0 = x1.
Definition term12 (a0 : Type') (x0 : nat) := fun y0 : nat => (fun y1 : nat => fun y2 : a0 => y1 = x0) y0.
Definition term40 (a0 : Type') (x0 : nat) := forall y0 : nat, ((@INJN a0 x0) = (@INJN a0 y0)) = (x0 = y0).
Definition term3 (a0 : Type') (x0 : nat) := @eq (nat -> a0 -> Prop) (fun y0 : nat => fun y1 : a0 => y0 = x0).
Definition term34 (a0 : Type') (x0 : a0) (x1 : nat) (x2 : nat) := (((fun y0 : nat => fun y1 : a0 => y0 = x1) x1 x0) = ((fun y0 : nat => fun y1 : a0 => y0 = x2) x1 x0)) -> x1 = x2.
Definition term32 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0) := imp (((fun y0 : nat => fun y1 : a0 => y0 = x1) x1 x2) = ((fun y0 : nat => fun y1 : a0 => y0 = x0) x1 x2)).
Definition term31 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0) := @eq Prop ((fun y0 : a0 => x0 = x1) x2).
Definition term37 (a0 : Type') (x0 : nat) (x1 : nat) := (x0 = x1) -> (@INJN a0 x0) = (@INJN a0 x1).
Definition term22 (a0 : Type') (x0 : a0) := @eq Prop ((fun y0 : a0 => True) x0).
Definition term33 (x0 : nat) (x1 : nat) := imp (x0 = x1).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term41 (a0 : Type') := forall y0 : nat, forall y1 : nat, ((@INJN a0 y0) = (@INJN a0 y1)) = (y0 = y1).
Definition term16 (a0 : Type') := fun y0 : a0 => True.
Definition term18 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term9 (a0 : Type') (x0 : type1597 a0) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term11 (a0 : Type') (x0 : nat) (x1 : nat) := fun y0 : a0 => x0 = x1.
Definition term27 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0) := (fun y0 : a0 => x0 = x1) x2.
Definition term4 (a0 : Type') (x0 : nat) := (fun y0 : nat => fun y1 : a0 => y0 = x0) x0.
Definition term20 (a0 : Type') := fun y0 : a0 => (fun y1 : a0 => True) y0.
Definition term30 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0) := @eq Prop ((fun y0 : a0 => (fun y1 : a0 => x0 = x1) y0) x2).
Definition term0 (a0 : Type') (x0 : nat) := (fun y0 : nat => (@INJN a0 y0) = (fun y1 : nat => fun y2 : a0 => y1 = y0)) x0.
Definition term6 (a0 : Type') (x0 : nat) (x1 : a0) := (fun y0 : nat => fun y1 : a0 => y0 = x0) x0 x1.
Definition term24 (a0 : Type') (x0 : nat) (x1 : nat) := (fun y0 : nat => (fun y1 : nat => fun y2 : a0 => y1 = x0) y0) x1.
Definition term23 (a0 : Type') (x0 : nat) (x1 : a0) := @eq Prop ((fun y0 : nat => fun y1 : a0 => y0 = x0) x0 x1).
Definition term7 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0) := (fun y0 : nat => fun y1 : a0 => y0 = x0) x1 x2.
Definition term39 (a0 : Type') (x0 : nat) (x1 : nat) := (((@INJN a0 x0) = (@INJN a0 x1)) -> x0 = x1) /\ ((x0 = x1) -> (@INJN a0 x0) = (@INJN a0 x1)).
Definition term25 (a0 : Type') (x0 : nat) (x1 : nat) := @eq (a0 -> Prop) ((fun y0 : nat => (fun y1 : nat => fun y2 : a0 => y1 = x0) y0) x1).
Definition term10 (a0 : Type') (x0 : nat) := (fun y0 : nat => (fun y1 : nat => fun y2 : a0 => y1 = x0) y0) x0.
Definition term2 (a0 : Type') (x0 : nat) := @eq (nat -> a0 -> Prop) (@INJN a0 x0).
Definition term5 (a0 : Type') (x0 : nat) (x1 : nat) := (fun y0 : nat => fun y1 : a0 => y0 = x0) x1.
Definition term1 (a0 : Type') (x0 : nat) := fun y0 : nat => fun y1 : a0 => y0 = x0.
Definition term36 (a0 : Type') (x0 : nat) (x1 : nat) := (((fun y0 : nat => fun y1 : a0 => y0 = x0) x0) = ((fun y0 : nat => fun y1 : a0 => y0 = x1) x0)) -> x0 = x1.
Definition term28 (a0 : Type') (x0 : nat) (x1 : nat) (x2 : a0) := (fun y0 : a0 => (fun y1 : a0 => x0 = x1) y0) x2.
Definition term38 (a0 : Type') (x0 : nat) (x1 : nat) := ((@INJN a0 x0) = (@INJN a0 x1)) -> x0 = x1.
Definition term17 (a0 : Type') (x0 : a0) := (fun y0 : a0 => True) x0.
Definition term13 (a0 : Type') (x0 : nat) := @eq (a0 -> Prop) ((fun y0 : nat => (fun y1 : nat => fun y2 : a0 => y1 = x0) y0) x0).
Definition term21 (a0 : Type') (x0 : a0) := @eq Prop ((fun y0 : a0 => (fun y1 : a0 => True) y0) x0).
