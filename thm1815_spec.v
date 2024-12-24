Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1815 : forall {A : Type'} (t : Prop), (fun t' : Prop => (forall x : A, t') = t') t.
