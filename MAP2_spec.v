Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1105126 : forall {_25542 _25543 _25549 : Type'} (h1' : _25543) (h2' : _25542) (f : _25543 -> _25542 -> _25549) (t1 : list _25543) (t2 : list _25542), ((@MAP2 _25549 _25543 _25542 f (@nil _25543) (@nil _25542)) = (@nil _25549)) /\ ((@MAP2 _25549 _25543 _25542 f (@cons _25543 h1' t1) (@cons _25542 h2' t2)) = (@cons _25549 (f h1' h2') (@MAP2 _25549 _25543 _25542 f t1 t2))).
