Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4374001 : forall {_105011 _105012 : Type'} (t : _105012 -> Prop) (f : (_105011 -> Prop) -> Prop) (h1 : f = (@EMPTY (_105011 -> Prop))), (forall p1 : _105011, forall p2 : _105012, ((@IN _105011 p1 (@INTERS _105011 (@EMPTY (_105011 -> Prop)))) /\ (@IN _105012 p2 t)) = ((@IN _105011 p1 (@UNIV _105011)) /\ (@IN _105012 p2 t))) = ((@CROSS _105012 _105011 (@INTERS _105011 f) t) = (@CROSS _105012 _105011 (@UNIV _105011) t)).
