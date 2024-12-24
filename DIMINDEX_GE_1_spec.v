Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7594654 : forall {A : Type'}, forall s : A -> Prop, Peano.le (NUMERAL (BIT1 0)) (@dimindex A s).
