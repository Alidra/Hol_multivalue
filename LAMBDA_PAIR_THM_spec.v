Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem51291 : forall {_5146 _5153 _5154 : Type'}, forall t : (prod _5154 _5153) -> _5146, (fun p : prod _5154 _5153 => t p) = (@GABS ((prod _5154 _5153) -> _5146) (fun f : (prod _5154 _5153) -> _5146 => forall x : _5154, forall y : _5153, @GEQ _5146 (f (@pair _5154 _5153 x y)) (t (@pair _5154 _5153 x y)))).
