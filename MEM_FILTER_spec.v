Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1152665 : forall {_27073 : Type'}, forall P : _27073 -> Prop, forall l : list _27073, forall x : _27073, (@List.In _27073 x (@FILTER _27073 P l)) = ((P x) /\ (@List.In _27073 x l)).
