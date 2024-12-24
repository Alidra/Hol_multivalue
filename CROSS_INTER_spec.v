Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4360794 : forall {_104453 _104454 _104486 _104487 : Type'}, (forall s : _104453 -> Prop, forall t : _104454 -> Prop, forall u : _104454 -> Prop, (@CROSS _104454 _104453 s (@INTER _104454 t u)) = (@INTER (prod _104453 _104454) (@CROSS _104454 _104453 s t) (@CROSS _104454 _104453 s u))) /\ (forall s : _104486 -> Prop, forall t : _104486 -> Prop, forall u : _104487 -> Prop, (@CROSS _104487 _104486 (@INTER _104486 s t) u) = (@INTER (prod _104486 _104487) (@CROSS _104487 _104486 s u) (@CROSS _104487 _104486 t u))).
