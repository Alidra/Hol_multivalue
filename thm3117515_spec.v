Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3117515 : forall {A : Type'} (P : Prop) (Q : A -> Prop), (fun Q' : A -> Prop => (P -> forall x : A, Q' x) = (forall x : A, P -> Q' x)) Q.
