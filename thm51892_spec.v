Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem51892 : forall {A B : Type'} (f : A -> B) (g : A -> B), (fun g' : A -> B => (f = g') = (forall x : A, (f x) = (g' x))) g.
