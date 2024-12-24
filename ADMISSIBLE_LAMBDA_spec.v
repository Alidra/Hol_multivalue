Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8131067 : forall {A B C P : Type'}, forall lt2 : A -> A -> Prop, forall p : (A -> B) -> P -> Prop, forall s : P -> A, forall t : (A -> B) -> C -> P -> Prop, (@admissible A B A Prop (prod C P) lt2 (fun f : A -> B => @GABS ((prod C P) -> Prop) (fun f' : (prod C P) -> Prop => forall u : C, forall x : P, @GEQ Prop (f' (@pair C P u x)) (p f x))) (@GABS ((prod C P) -> A) (fun f : (prod C P) -> A => forall u : C, forall x : P, @GEQ A (f (@pair C P u x)) (s x))) (fun f : A -> B => @GABS ((prod C P) -> Prop) (fun f' : (prod C P) -> Prop => forall u : C, forall x : P, @GEQ Prop (f' (@pair C P u x)) (t f u x)))) -> @admissible A B A (C -> Prop) P lt2 p s (fun f : A -> B => fun x : P => fun u : C => t f u x).
