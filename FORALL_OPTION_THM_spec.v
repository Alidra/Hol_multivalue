Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1072225 : forall {_24424 : Type'}, forall P : (option _24424) -> Prop, (forall x : option _24424, P x) = ((P (@None _24424)) /\ (forall a : _24424, P (@Some _24424 a))).
