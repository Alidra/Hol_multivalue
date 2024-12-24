Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3211605 : forall {A : Type'}, forall s : A -> Prop, (~ (s = (@EMPTY A))) -> @IN A (@CHOICE A s) s.
