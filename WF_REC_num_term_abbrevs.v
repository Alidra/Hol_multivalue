Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (a0 : Type') (x0 : type972 a0) := (fun y0 : type972 a0 => (forall y1 : nat -> a0, forall y2 : nat -> a0, forall y3 : nat, (forall y4 : nat, (Peano.lt y4 y3) -> (y1 y4) = (y2 y4)) -> (y0 y1 y3) = (y0 y2 y3)) -> exists y1 : nat -> a0, forall y2 : nat, (y1 y2) = (y0 y1 y2)) x0.
Definition term3 (a0 : Type') := forall y0 : type972 a0, (forall y1 : nat -> a0, forall y2 : nat -> a0, forall y3 : nat, (forall y4 : nat, (Peano.lt y4 y3) -> (y1 y4) = (y2 y4)) -> (y0 y1 y3) = (y0 y2 y3)) -> exists y1 : nat -> a0, forall y2 : nat, (y1 y2) = (y0 y1 y2).
Definition term5 (a0 : Type') (x0 : type972 a0) := (forall y0 : nat -> a0, forall y1 : nat -> a0, forall y2 : nat, (forall y3 : nat, (Peano.lt y3 y2) -> (y0 y3) = (y1 y3)) -> (x0 y0 y2) = (x0 y1 y2)) -> exists y0 : nat -> a0, forall y1 : nat, (y0 y1) = (x0 y0 y1).
Definition term1 (a0 : Type') (x0 : type1605) := (@WF nat x0) -> forall y0 : type972 a0, (forall y1 : nat -> a0, forall y2 : nat -> a0, forall y3 : nat, (forall y4 : nat, (x0 y4 y3) -> (y1 y4) = (y2 y4)) -> (y0 y1 y3) = (y0 y2 y3)) -> exists y1 : nat -> a0, forall y2 : nat, (y1 y2) = (y0 y1 y2).
Definition term0 (a0 : Type') (a1 : Type') (x0 : type1402 a0) := (@WF a0 x0) -> forall y0 : type549 a0 a1, (forall y1 : a0 -> a1, forall y2 : a0 -> a1, forall y3 : a0, (forall y4 : a0, (x0 y4 y3) -> (y1 y4) = (y2 y4)) -> (y0 y1 y3) = (y0 y2 y3)) -> exists y1 : a0 -> a1, forall y2 : a0, (y1 y2) = (y0 y1 y2).
Definition term2 (a0 : Type') := (@WF nat Peano.lt) -> forall y0 : type972 a0, (forall y1 : nat -> a0, forall y2 : nat -> a0, forall y3 : nat, (forall y4 : nat, (Peano.lt y4 y3) -> (y1 y4) = (y2 y4)) -> (y0 y1 y3) = (y0 y2 y3)) -> exists y1 : nat -> a0, forall y2 : nat, (y1 y2) = (y0 y1 y2).
