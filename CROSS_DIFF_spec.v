Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4362404 : forall {_104591 _104592 _104624 _104625 : Type'}, (forall s : _104591 -> Prop, forall t : _104592 -> Prop, forall u : _104592 -> Prop, (@CROSS _104592 _104591 s (@DIFF _104592 t u)) = (@DIFF (prod _104591 _104592) (@CROSS _104592 _104591 s t) (@CROSS _104592 _104591 s u))) /\ (forall s : _104624 -> Prop, forall t : _104624 -> Prop, forall u : _104625 -> Prop, (@CROSS _104625 _104624 (@DIFF _104624 s t) u) = (@DIFF (prod _104624 _104625) (@CROSS _104625 _104624 s u) (@CROSS _104625 _104624 t u))).
