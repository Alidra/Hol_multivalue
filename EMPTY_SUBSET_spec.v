Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3219985 : forall {A : Type'}, forall s : A -> Prop, @SUBSET A (@EMPTY A) s.
