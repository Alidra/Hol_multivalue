Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4361537 : forall {_104522 _104523 _104555 _104556 : Type'}, (forall s : _104522 -> Prop, forall t : _104523 -> Prop, forall u : _104523 -> Prop, (@CROSS _104523 _104522 s (@UNION _104523 t u)) = (@UNION (prod _104522 _104523) (@CROSS _104523 _104522 s t) (@CROSS _104523 _104522 s u))) /\ (forall s : _104555 -> Prop, forall t : _104555 -> Prop, forall u : _104556 -> Prop, (@CROSS _104556 _104555 (@UNION _104555 s t) u) = (@UNION (prod _104555 _104556) (@CROSS _104556 _104555 s u) (@CROSS _104556 _104555 t u))).
