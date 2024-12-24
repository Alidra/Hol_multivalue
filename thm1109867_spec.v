Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1109867 : forall {_25786 _25787 : Type'}, forall h : _25787, forall f : _25787 -> _25786 -> Prop, forall t : list _25787, forall l : list _25786, (@ALLPAIRS _25786 _25787 f (@cons _25787 h t) l) = ((@List.Forall _25786 (f h) l) /\ (@ALLPAIRS _25786 _25787 f t l)).
