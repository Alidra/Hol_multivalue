Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8126036 : forall {A B C D P : Type'}, forall lt2 : A -> A -> Prop, forall p : (A -> B) -> P -> Prop, forall s : P -> A, forall g : P -> C -> D, forall y : (A -> B) -> P -> C, (@admissible A B A C P lt2 p s y) -> @admissible A B A D P lt2 p s (fun f : A -> B => fun x : P => g x (y f x)).
