Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8037491 : forall {_142469 _142470 _142471 _142505 _142506 _142507 : Type'}, (forall s : (cart _142469 _142470) -> Prop, forall t : (cart _142469 _142471) -> Prop, forall u : (cart _142469 _142471) -> Prop, (@PCROSS _142469 _142470 _142471 s (@INTER (cart _142469 _142471) t u)) = (@INTER (cart _142469 (finite_sum _142470 _142471)) (@PCROSS _142469 _142470 _142471 s t) (@PCROSS _142469 _142470 _142471 s u))) /\ (forall s : (cart _142505 _142506) -> Prop, forall t : (cart _142505 _142506) -> Prop, forall u : (cart _142505 _142507) -> Prop, (@PCROSS _142505 _142506 _142507 (@INTER (cart _142505 _142506) s t) u) = (@INTER (cart _142505 (finite_sum _142506 _142507)) (@PCROSS _142505 _142506 _142507 s u) (@PCROSS _142505 _142506 _142507 t u))).
