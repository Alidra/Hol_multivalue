Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3311905 : forall {A : Type'}, forall x : A, forall s : A -> Prop, forall t : A -> Prop, (@SUBSET A s (@INSERT A x t)) = (@SUBSET A (@DELETE A s x) t).
