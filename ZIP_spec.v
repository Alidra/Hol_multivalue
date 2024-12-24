Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1109008 : forall {_25738 _25739 _25763 _25764 : Type'} (h1' : _25763) (h2' : _25764) (t1 : list _25763) (t2 : list _25764), ((@ZIP _25738 _25739 (@nil _25738) (@nil _25739)) = (@nil (prod _25738 _25739))) /\ ((@ZIP _25763 _25764 (@cons _25763 h1' t1) (@cons _25764 h2' t2)) = (@cons (prod _25763 _25764) (@pair _25763 _25764 h1' h2') (@ZIP _25763 _25764 t1 t2))).
