Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1108290 : forall {_25687 _25688 _25689 : Type'} (h1' : _25689) (h2' : _25688) (f : _25689 -> _25688 -> _25687 -> _25687) (t1 : list _25689) (t2 : list _25688) (b : _25687), ((@ITLIST2 _25687 _25689 _25688 f (@nil _25689) (@nil _25688) b) = b) /\ ((@ITLIST2 _25687 _25689 _25688 f (@cons _25689 h1' t1) (@cons _25688 h2' t2) b) = (f h1' h2' (@ITLIST2 _25687 _25689 _25688 f t1 t2 b))).
