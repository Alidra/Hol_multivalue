Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem48920 : forall {_5076 : Type'} (P : _5076 -> Prop), True = ((ex P) -> P (@GABS _5076 P)).
