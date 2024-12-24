Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3313024 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall x : A, (@DIFF A s (@INSERT A x t)) = (@DIFF A (@DELETE A s x) t).
