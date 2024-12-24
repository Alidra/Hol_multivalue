Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem51073 : forall {_5146 _5153 _5154 : Type'} (t : (prod _5154 _5153) -> _5146) (p1 : _5154) (p2 : _5153), (@eq _5146 ((fun p : prod _5154 _5153 => t p) (@pair _5154 _5153 p1 p2))) = (@eq _5146 (t (@pair _5154 _5153 p1 p2))).
