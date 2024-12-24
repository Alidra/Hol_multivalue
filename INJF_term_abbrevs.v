Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (a0 : Type') (x0 : type1600 a0) := (fun y0 : type1600 a0 => (@INJF a0 y0) = (fun y1 : nat => y0 (NUMFST y1) (NUMSND y1))) x0.
Definition term1 (a0 : Type') (x0 : type1600 a0) := (fun y0 : type1600 a0 => fun y1 : nat => y0 (NUMFST y1) (NUMSND y1)) x0.
Definition term0 (a0 : Type') := fun y0 : type1600 a0 => fun y1 : nat => y0 (NUMFST y1) (NUMSND y1).
Definition term3 (a0 : Type') := forall y0 : type1600 a0, (@INJF a0 y0) = (fun y1 : nat => y0 (NUMFST y1) (NUMSND y1)).
Definition term2 (a0 : Type') (x0 : type1600 a0) := fun y0 : nat => x0 (NUMFST y0) (NUMSND y0).
