Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem9307 : forall {A : Type'}, (@ex A) = (fun P : A -> Prop => P (@ε A P)).
