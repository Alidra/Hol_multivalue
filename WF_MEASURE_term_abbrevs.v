Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (a0 : Type') (a1 : Type') (x0 : type1402 a1) := forall y0 : a0 -> a1, (@WF a1 x0) -> @WF a0 (fun y1 : a0 => fun y2 : a0 => x0 (y0 y1) (y0 y2)).
Definition term6 (a0 : Type') (a1 : Type') (x0 : type1402 a1) (x1 : a0 -> a1) := (forall y0 : type1402 a1, forall y1 : a0 -> a1, (@WF a1 y0) -> @WF a0 (fun y2 : a0 => fun y3 : a0 => y0 (y1 y2) (y1 y3))) -> @WF a0 (fun y0 : a0 => fun y1 : a0 => x0 (x1 y0) (x1 y1)).
Definition term3 (a0 : Type') (a1 : Type') (x0 : type1402 a1) (x1 : a0 -> a1) := (fun y0 : a0 -> a1 => (@WF a1 x0) -> @WF a0 (fun y1 : a0 => fun y2 : a0 => x0 (y0 y1) (y0 y2))) x1.
Definition term7 (a0 : Type') (a1 : Type') := (forall y0 : type1402 a1, forall y1 : a0 -> a1, (@WF a1 y0) -> @WF a0 (fun y2 : a0 => fun y3 : a0 => y0 (y1 y2) (y1 y3))) -> forall y0 : type1402 a1, forall y1 : a0 -> a1, (@WF a1 y0) -> @WF a0 (fun y2 : a0 => fun y3 : a0 => y0 (y1 y2) (y1 y3)).
Definition term11 (a0 : Type') (x0 : a0 -> nat) := @WF a0 (fun y0 : a0 => fun y1 : a0 => Peano.lt (x0 y0) (x0 y1)).
Definition term13 (a0 : Type') (x0 : a0 -> nat) := (@WF nat Peano.lt) -> @WF a0 (fun y0 : a0 => fun y1 : a0 => Peano.lt (x0 y0) (x0 y1)).
Definition term5 (a0 : Type') (a1 : Type') (x0 : type1402 a1) (x1 : a0 -> a1) := @WF a0 (fun y0 : a0 => fun y1 : a0 => x0 (x1 y0) (x1 y1)).
Definition term0 (a0 : Type') (a1 : Type') := forall y0 : type1402 a1, forall y1 : a0 -> a1, (@WF a1 y0) -> @WF a0 (fun y2 : a0 => fun y3 : a0 => y0 (y1 y2) (y1 y3)).
Definition term12 (a0 : Type') (x0 : type1605) (x1 : a0 -> nat) := (@WF nat x0) -> @WF a0 (fun y0 : a0 => fun y1 : a0 => x0 (x1 y0) (x1 y1)).
Definition term4 (a0 : Type') (a1 : Type') (x0 : type1402 a1) (x1 : a0 -> a1) := (@WF a1 x0) -> @WF a0 (fun y0 : a0 => fun y1 : a0 => x0 (x1 y0) (x1 y1)).
Definition term9 (a0 : Type') (x0 : a0 -> nat) := fun y0 : a0 => fun y1 : a0 => Peano.lt (x0 y0) (x0 y1).
Definition term1 (a0 : Type') (a1 : Type') (x0 : type1402 a1) := (fun y0 : type1402 a1 => forall y1 : a0 -> a1, (@WF a1 y0) -> @WF a0 (fun y2 : a0 => fun y3 : a0 => y0 (y1 y2) (y1 y3))) x0.
Definition term10 (a0 : Type') (x0 : a0 -> nat) := @WF a0 (@MEASURE a0 x0).
Definition term8 (a0 : Type') (x0 : a0 -> nat) := (fun y0 : a0 -> nat => (@MEASURE a0 y0) = (fun y1 : a0 => fun y2 : a0 => Peano.lt (y0 y1) (y0 y2))) x0.
Definition term14 (a0 : Type') := forall y0 : a0 -> nat, @WF a0 (@MEASURE a0 y0).
