Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7068426 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall f : A -> real, ((@FINITE A s) /\ (@FINITE A t)) -> (real_add (@sum A s f) (@sum A t f)) = (real_add (@sum A (@UNION A s t) f) (@sum A (@INTER A s t) f)).
