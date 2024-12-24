Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7590231 : forall {A : Type'}, forall s : A -> Prop, (@dimindex A s) = (@COND nat (@FINITE A (@UNIV A)) (@CARD A (@UNIV A)) (NUMERAL (BIT1 0))).
