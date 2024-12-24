Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4334566 : forall {_104151 _104152 : Type'}, forall P : (prod _104152 _104151) -> Prop, forall s : _104152 -> Prop, forall t : _104151 -> Prop, (exists z : prod _104152 _104151, (@IN (prod _104152 _104151) z (@CROSS _104151 _104152 s t)) /\ (P z)) = (exists x : _104152, exists y : _104151, (@IN _104152 x s) /\ ((@IN _104151 y t) /\ (P (@pair _104152 _104151 x y)))).
