Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem23443 : forall {A : Type'}, forall x : A, (@ε A (fun y : A => x = y)) = x.
