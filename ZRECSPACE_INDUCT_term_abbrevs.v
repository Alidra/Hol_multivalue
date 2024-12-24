Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := forall y0 : type953 a0, ((y0 (@ZBOT a0)) /\ (forall y1 : nat, forall y2 : a0, forall y3 : type1600 a0, (forall y4 : nat, y0 (y3 y4)) -> y0 (@ZCONSTR a0 y1 y2 y3))) -> forall y1 : type1597 a0, (@ZRECSPACE a0 y1) -> y0 y1.
