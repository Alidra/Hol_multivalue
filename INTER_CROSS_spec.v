Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4362894 : forall {_104663 _104666 : Type'}, forall s : _104663 -> Prop, forall s' : _104663 -> Prop, forall t : _104666 -> Prop, forall t' : _104666 -> Prop, (@INTER (prod _104663 _104666) (@CROSS _104666 _104663 s t) (@CROSS _104666 _104663 s' t')) = (@CROSS _104666 _104663 (@INTER _104663 s s') (@INTER _104666 t t')).
