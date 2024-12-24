Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3202678 : forall {A B : Type'}, forall f : A -> B, forall s : A -> Prop, forall t : B -> Prop, (@BIJ A B f s t) = ((@INJ A B f s t) /\ (@SURJ A B f s t)).
