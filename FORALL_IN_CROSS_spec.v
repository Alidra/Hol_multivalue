Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4334371 : forall {_104099 _104100 : Type'}, forall P : (prod _104100 _104099) -> Prop, forall s : _104100 -> Prop, forall t : _104099 -> Prop, (forall z : prod _104100 _104099, (@IN (prod _104100 _104099) z (@CROSS _104099 _104100 s t)) -> P z) = (forall x : _104100, forall y : _104099, ((@IN _104100 x s) /\ (@IN _104099 y t)) -> P (@pair _104100 _104099 x y)).
