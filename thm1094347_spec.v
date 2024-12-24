Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1094347 : forall {A : Type'} (P : (list A) -> Prop), ((fun P' : (list A) -> Prop => ((P' (@nil A)) /\ (forall h : A, forall t : list A, (P' t) -> P' (@cons A h t))) -> forall l : list A, P' l) P) = (((P (@nil A)) /\ (forall h : A, forall t : list A, (P t) -> P (@cons A h t))) -> forall l : list A, P l).
