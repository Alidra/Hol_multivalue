Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term16 (a0 : Type') (x0 : type1600 a0) (x1 : type1600 a0) (x2 : nat) := fun y0 : nat => (x0 x2 y0) = (x1 x2 y0).
Definition term46 (a0 : Type') (x0 : type1600 a0) (x1 : type1600 a0) := (((@INJF a0 x0) = (@INJF a0 x1)) -> x0 = x1) /\ ((x0 = x1) -> (@INJF a0 x0) = (@INJF a0 x1)).
Definition term4 (a0 : Type') (x0 : type1600 a0) := (fun y0 : type1600 a0 => (@INJF a0 y0) = (fun y1 : nat => y0 (NUMFST y1) (NUMSND y1))) x0.
Definition term43 (a0 : Type') (x0 : type1600 a0) (x1 : type1600 a0) (x2 : nat) (x3 : nat) (x4 : a0) := ((fun y0 : nat => x0 (NUMFST y0) (NUMSND y0)) = (fun y0 : nat => x1 (NUMFST y0) (NUMSND y0))) -> (x0 x2 x3 x4) = (x1 x2 x3 x4).
Definition term31 (a0 : Type') (x0 : type1600 a0) (x1 : nat) (x2 : nat) := @eq (a0 -> Prop) ((fun y0 : nat => (fun y1 : nat => x0 (NUMFST y1) (NUMSND y1)) y0) (NUMPAIR x1 x2)).
Definition term3 (x0 : nat) (x1 : nat) := ((NUMFST (NUMPAIR x0 x1)) = x0) /\ ((NUMSND (NUMPAIR x0 x1)) = x1).
Definition term44 (a0 : Type') (x0 : type1600 a0) (x1 : type1600 a0) := (x0 = x1) -> (@INJF a0 x0) = (@INJF a0 x1).
Definition term1 (x0 : nat) := forall y0 : nat, ((NUMFST (NUMPAIR x0 y0)) = x0) /\ ((NUMSND (NUMPAIR x0 y0)) = y0).
Definition term38 (a0 : Type') (x0 : type1600 a0) (x1 : nat) (x2 : nat) (x3 : a0) := @eq Prop (x0 x1 x2 x3).
Definition term40 (a0 : Type') (x0 : type1600 a0) (x1 : type1600 a0) (x2 : nat) (x3 : nat) (x4 : a0) := imp ((x0 x2 x3 x4) = (x1 x2 x3 x4)).
Definition term36 (x0 : nat) (x1 : nat) := NUMSND (NUMPAIR x0 x1).
Definition term19 (a0 : Type') (x0 : type1600 a0) (x1 : type1600 a0) := fun y0 : nat => (x0 y0) = (x1 y0).
Definition term12 (a0 : Type') (x0 : type1597 a0) (x1 : type1597 a0) := forall y0 : nat, (x0 y0) = (x1 y0).
Definition term11 (a0 : Type') (x0 : type1600 a0) (x1 : type1600 a0) := forall y0 : nat, (x0 y0) = (x1 y0).
Definition term25 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0) := (fun y0 : a0 => x0 y0) x1.
Definition term21 (a0 : Type') (x0 : type1600 a0) (x1 : type1600 a0) := forall y0 : nat, forall y1 : nat, forall y2 : a0, (x0 y0 y1 y2) = (x1 y0 y1 y2).
Definition term18 (a0 : Type') (x0 : type1600 a0) (x1 : type1600 a0) (x2 : nat) := forall y0 : nat, forall y1 : a0, (x0 x2 y0 y1) = (x1 x2 y0 y1).
Definition term29 (a0 : Type') (x0 : type1600 a0) (x1 : nat) := x0 (NUMFST x1) (NUMSND x1).
Definition term28 (a0 : Type') (x0 : type1600 a0) (x1 : nat) := (fun y0 : nat => x0 (NUMFST y0) (NUMSND y0)) x1.
Definition term26 (a0 : Type') (x0 : type1597 a0) (x1 : nat) := (fun y0 : nat => x0 y0) x1.
Definition term5 (a0 : Type') (x0 : type1600 a0) := fun y0 : nat => x0 (NUMFST y0) (NUMSND y0).
Definition term42 (a0 : Type') (x0 : type1600 a0) (x1 : type1600 a0) (x2 : nat) (x3 : nat) (x4 : a0) := ((x0 x2 x3 x4) = (x1 x2 x3 x4)) -> (x0 x2 x3 x4) = (x1 x2 x3 x4).
Definition term13 (a0 : Type') (x0 : type1600 a0) (x1 : type1600 a0) (x2 : nat) := forall y0 : nat, (x0 x2 y0) = (x1 x2 y0).
Definition term39 (a0 : Type') (x0 : type1600 a0) (x1 : type1600 a0) (x2 : nat) (x3 : nat) (x4 : a0) := imp (((fun y0 : nat => x0 (NUMFST y0) (NUMSND y0)) (NUMPAIR x2 x3) x4) = ((fun y0 : nat => x1 (NUMFST y0) (NUMSND y0)) (NUMPAIR x2 x3) x4)).
Definition term41 (a0 : Type') (x0 : type1600 a0) (x1 : type1600 a0) (x2 : nat) (x3 : nat) (x4 : a0) := (((fun y0 : nat => x0 (NUMFST y0) (NUMSND y0)) (NUMPAIR x2 x3) x4) = ((fun y0 : nat => x1 (NUMFST y0) (NUMSND y0)) (NUMPAIR x2 x3) x4)) -> (x0 x2 x3 x4) = (x1 x2 x3 x4).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((NUMFST (NUMPAIR x0 y0)) = x0) /\ ((NUMSND (NUMPAIR x0 y0)) = y0)) x1.
Definition term15 (a0 : Type') (x0 : type1600 a0) (x1 : type1600 a0) (x2 : nat) (x3 : nat) := forall y0 : a0, (x0 x2 x3 y0) = (x1 x2 x3 y0).
Definition term27 (a0 : Type') (x0 : type1600 a0) (x1 : nat) (x2 : nat) := (fun y0 : nat => (fun y1 : nat => x0 (NUMFST y1) (NUMSND y1)) y0) (NUMPAIR x1 x2).
Definition term47 (a0 : Type') (x0 : type1600 a0) := forall y0 : type1600 a0, ((@INJF a0 x0) = (@INJF a0 y0)) = (x0 = y0).
Definition term24 (a0 : Type') (x0 : type1600 a0) (x1 : nat) (x2 : nat) (x3 : a0) := (fun y0 : nat => x0 (NUMFST y0) (NUMSND y0)) (NUMPAIR x1 x2) x3.
Definition term32 (a0 : Type') (x0 : type1600 a0) (x1 : nat) (x2 : nat) := @eq (a0 -> Prop) ((fun y0 : nat => x0 (NUMFST y0) (NUMSND y0)) (NUMPAIR x1 x2)).
Definition term10 (a0 : Type') (x0 : type1600 a0) := @eq (nat -> a0 -> Prop) (@INJF a0 x0).
Definition term48 (a0 : Type') := forall y0 : type1600 a0, forall y1 : type1600 a0, ((@INJF a0 y0) = (@INJF a0 y1)) = (y0 = y1).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((NUMFST (NUMPAIR y0 y1)) = y0) /\ ((NUMSND (NUMPAIR y0 y1)) = y1)) x0.
Definition term30 (a0 : Type') (x0 : type1600 a0) := fun y0 : nat => (fun y1 : nat => x0 (NUMFST y1) (NUMSND y1)) y0.
Definition term34 (x0 : nat) (x1 : nat) := NUMFST (NUMPAIR x0 x1).
Definition term33 (a0 : Type') (x0 : type1600 a0) (x1 : nat) (x2 : nat) := x0 (NUMFST (NUMPAIR x1 x2)) (NUMSND (NUMPAIR x1 x2)).
Definition term45 (a0 : Type') (x0 : type1600 a0) (x1 : type1600 a0) := ((@INJF a0 x0) = (@INJF a0 x1)) -> x0 = x1.
Definition term23 (a0 : Type') (x0 : type1600 a0) (x1 : nat) (x2 : nat) := (fun y0 : nat => x0 (NUMFST y0) (NUMSND y0)) (NUMPAIR x1 x2).
Definition term14 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := forall y0 : a0, (x0 y0) = (x1 y0).
Definition term9 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := forall y0 : a0, (x0 y0) = (x1 y0).
Definition term17 (a0 : Type') (x0 : type1600 a0) (x1 : type1600 a0) (x2 : nat) := fun y0 : nat => forall y1 : a0, (x0 x2 y0 y1) = (x1 x2 y0 y1).
Definition term6 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := (fun y0 : a0 -> a1 => forall y1 : a0 -> a1, (y0 = y1) = (forall y2 : a0, (y0 y2) = (y1 y2))) x0.
Definition term22 (a0 : Type') (x0 : type1600 a0) := @eq (nat -> a0 -> Prop) (fun y0 : nat => x0 (NUMFST y0) (NUMSND y0)).
Definition term37 (a0 : Type') (x0 : type1600 a0) (x1 : nat) (x2 : nat) (x3 : a0) := @eq Prop ((fun y0 : nat => x0 (NUMFST y0) (NUMSND y0)) (NUMPAIR x1 x2) x3).
Definition term8 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1))) x1.
Definition term35 (a0 : Type') (x0 : type1600 a0) (x1 : nat) (x2 : nat) := x0 (NUMFST (NUMPAIR x1 x2)).
Definition term7 (a0 : Type') (a1 : Type') (x0 : a0 -> a1) := forall y0 : a0 -> a1, (x0 = y0) = (forall y1 : a0, (x0 y1) = (y0 y1)).
Definition term20 (a0 : Type') (x0 : type1600 a0) (x1 : type1600 a0) := fun y0 : nat => forall y1 : nat, forall y2 : a0, (x0 y0 y1 y2) = (x1 y0 y1 y2).
