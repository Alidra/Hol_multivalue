Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8291440 : forall {A B P : Type'}, forall lt2 : A -> A -> Prop, forall p : (A -> B) -> P -> Prop, forall P' : (A -> B) -> P -> Prop, forall s : P -> A, forall h : (A -> B) -> P -> B, forall k : (A -> B) -> P -> B, ((@admissible A B A Prop P lt2 p s P') /\ ((@superadmissible A B P lt2 (fun f : A -> B => fun x : P => (p f x) /\ (P' f x)) s h) /\ (@superadmissible A B P lt2 (fun f : A -> B => fun x : P => (p f x) /\ (~ (P' f x))) s k))) -> @superadmissible A B P lt2 p s (fun f : A -> B => fun x : P => @COND B (P' f x) (h f x) (k f x)).
