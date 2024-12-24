Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1116558 : forall {A : Type'}, forall l : list A, forall m : list A, (@List.length A (@List.app A l m)) = (Nat.add (@List.length A l) (@List.length A m)).
