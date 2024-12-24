Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3269122 : forall {A : Type'}, (forall s : A -> Prop, forall a : A, (@DISJOINT A s (@INSERT A a (@EMPTY A))) = (~ (@IN A a s))) /\ (forall s : A -> Prop, forall a : A, (@DISJOINT A (@INSERT A a (@EMPTY A)) s) = (~ (@IN A a s))).
