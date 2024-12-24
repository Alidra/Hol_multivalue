Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4393895 : forall {A B C : Type'}, forall f : A -> B, forall g : B -> C, forall s : A -> Prop, forall t : B -> Prop, (@SUBSET B (@IMAGE A B f s) t) -> (@RESTRICTION A C s (@o A B C (@RESTRICTION B C t g) (@RESTRICTION A B s f))) = (@RESTRICTION A C s (@o A B C g f)).
