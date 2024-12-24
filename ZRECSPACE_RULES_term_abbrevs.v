Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := (@ZRECSPACE a0 (@ZBOT a0)) /\ (forall y0 : nat, forall y1 : a0, forall y2 : type1600 a0, (forall y3 : nat, @ZRECSPACE a0 (y2 y3)) -> @ZRECSPACE a0 (@ZCONSTR a0 y0 y1 y2)).
