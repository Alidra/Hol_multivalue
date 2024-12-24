Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3270825 : forall {A : Type'}, forall s : A -> Prop, (@DIFF A (@UNIV A) (@DIFF A (@UNIV A) s)) = s.
