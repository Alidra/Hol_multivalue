Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem9306 : forall {A : Type'}, forall x : A -> Prop, (ex x) = ((fun P : A -> Prop => P (@ε A P)) x).
