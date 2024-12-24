Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (a0 : Type') (a1 : Type') (x0 : list a0) := (fun y0 : list a0 => @lambda a0 a1 (fun y1 : nat => @EL a0 (Nat.sub y1 (NUMERAL (BIT1 0))) y0)) x0.
Definition term2 (a0 : Type') (a1 : Type') (x0 : list a0) := @lambda a0 a1 (fun y0 : nat => @EL a0 (Nat.sub y0 (NUMERAL (BIT1 0))) x0).
Definition term0 (a0 : Type') (a1 : Type') := fun y0 : list a0 => @lambda a0 a1 (fun y1 : nat => @EL a0 (Nat.sub y1 (NUMERAL (BIT1 0))) y0).
Definition term3 (a0 : Type') (a1 : Type') := forall y0 : list a0, (@vector a0 a1 y0) = (@lambda a0 a1 (fun y1 : nat => @EL a0 (Nat.sub y1 (NUMERAL (BIT1 0))) y0)).
Definition term4 (a0 : Type') (a1 : Type') (x0 : list a0) := (fun y0 : list a0 => (@vector a0 a1 y0) = (@lambda a0 a1 (fun y1 : nat => @EL a0 (Nat.sub y1 (NUMERAL (BIT1 0))) y0))) x0.
