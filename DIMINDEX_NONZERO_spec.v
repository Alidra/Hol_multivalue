Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7591719 : forall {A : Type'}, forall s : A -> Prop, ~ ((@dimindex A s) = (NUMERAL 0)).
