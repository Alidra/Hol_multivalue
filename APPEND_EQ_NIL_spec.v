Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1187397 : forall {_27653 : Type'}, forall l : list _27653, forall m : list _27653, ((@List.app _27653 l m) = (@nil _27653)) = ((l = (@nil _27653)) /\ (m = (@nil _27653))).
