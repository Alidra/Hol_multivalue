Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1109874 : forall {_25786 _25787 : Type'} (f : _25787 -> _25786 -> Prop) (l : list _25786), (@ALLPAIRS _25786 _25787 f (@nil _25787) l) = True.
