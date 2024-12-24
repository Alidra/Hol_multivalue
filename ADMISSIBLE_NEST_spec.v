Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8133916 : forall {A B P : Type'}, forall lt2 : A -> A -> Prop, forall p : (A -> B) -> P -> Prop, forall s : P -> A, forall t : (A -> B) -> P -> A, ((@admissible A B A A P lt2 p s t) /\ (forall f : A -> B, forall a : P, (p f a) -> lt2 (t f a) (s a))) -> @admissible A B A B P lt2 p s (fun f : A -> B => fun x : P => f (t f x)).
