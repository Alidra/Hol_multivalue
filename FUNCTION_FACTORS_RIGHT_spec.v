Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3584054 : forall {_91882 _91894 _91895 : Type'}, forall f : _91894 -> _91895, forall g : _91882 -> _91895, (forall x : _91894, exists y : _91882, (g y) = (f x)) = (exists h : _91894 -> _91882, f = (@o _91894 _91882 _91895 g h)).
