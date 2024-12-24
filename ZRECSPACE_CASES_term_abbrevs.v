Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (a0 : Type') := forall y0 : type1597 a0, (@ZRECSPACE a0 y0) = ((y0 = (@ZBOT a0)) \/ (exists y1 : nat, exists y2 : a0, exists y3 : type1600 a0, (y0 = (@ZCONSTR a0 y1 y2 y3)) /\ (forall y4 : nat, @ZRECSPACE a0 (y3 y4)))).
