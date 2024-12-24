Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3245541 : forall {A : Type'} (P : (A -> Prop) -> Prop), forall t : A -> Prop, forall u : A -> Prop, (forall s : A -> Prop, (@SUBSET A s (@UNION A t u)) -> P s) = (forall t' : A -> Prop, forall u' : A -> Prop, ((@SUBSET A t' t) /\ (@SUBSET A u' u)) -> P (@UNION A t' u')).
