Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1107273 : forall {_25617 _25623 : Type'} (h : prod _25623 _25617) (a : _25623) (t : list (prod _25623 _25617)), ((fun t' : list (prod _25623 _25617) => (@ASSOC _25617 _25623 a (@cons (prod _25623 _25617) h t')) = (@COND _25617 ((@fst _25623 _25617 h) = a) (@snd _25623 _25617 h) (@ASSOC _25617 _25623 a t'))) t) = ((@ASSOC _25617 _25623 a (@cons (prod _25623 _25617) h t)) = (@COND _25617 ((@fst _25623 _25617 h) = a) (@snd _25623 _25617 h) (@ASSOC _25617 _25623 a t))).
