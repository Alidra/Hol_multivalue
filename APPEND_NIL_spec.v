Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1111732 : forall {A : Type'}, forall l : list A, (@List.app A l (@nil A)) = l.
