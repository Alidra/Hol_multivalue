Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1075149 : forall {A B : Type'}, forall g : B -> A, forall f : A -> B, (@ExtensionalityFacts.is_inverse A B f g) = ((forall x : B, (f (g x)) = x) /\ (forall y : A, (g (f y)) = y)).
