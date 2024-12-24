Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8091832 : forall {A B C P : Type'}, forall clauses : list (prod (P -> A) (C -> P -> B)), forall c : C, (forall s : P -> A, forall t : C -> P -> B, forall s' : P -> A, forall t' : C -> P -> B, forall x : P, forall y : P, ((@List.In (prod (P -> A) (C -> P -> B)) (@pair (P -> A) (C -> P -> B) s t) clauses) /\ ((@List.In (prod (P -> A) (C -> P -> B)) (@pair (P -> A) (C -> P -> B) s' t') clauses) /\ ((s x) = (s' y)))) -> (t c x) = (t' c y)) -> @List.Forall (prod (P -> A) (C -> P -> B)) (@GABS ((prod (P -> A) (C -> P -> B)) -> Prop) (fun f : (prod (P -> A) (C -> P -> B)) -> Prop => forall s : P -> A, forall t : C -> P -> B, @GEQ Prop (f (@pair (P -> A) (C -> P -> B) s t)) (forall x : P, (@CASEWISE B P A C clauses c (s x)) = (t c x)))) clauses.
