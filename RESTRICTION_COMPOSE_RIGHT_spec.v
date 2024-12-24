Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4393235 : forall {A B C : Type'}, forall f : A -> B, forall g : B -> C, forall s : A -> Prop, (@RESTRICTION A C s (@o A B C g (@RESTRICTION A B s f))) = (@RESTRICTION A C s (@o A B C g f)).
