Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem51057 : forall {_5146 _5153 _5154 : Type'} (t : (prod _5154 _5153) -> _5146), ((fun p : prod _5154 _5153 => t p) = (@GABS ((prod _5154 _5153) -> _5146) (fun f : (prod _5154 _5153) -> _5146 => forall x : _5154, forall y : _5153, @GEQ _5146 (f (@pair _5154 _5153 x y)) (t (@pair _5154 _5153 x y))))) = (forall p1 : _5154, forall p2 : _5153, ((fun p : prod _5154 _5153 => t p) (@pair _5154 _5153 p1 p2)) = (@GABS ((prod _5154 _5153) -> _5146) (fun f : (prod _5154 _5153) -> _5146 => forall x : _5154, forall y : _5153, @GEQ _5146 (f (@pair _5154 _5153 x y)) (t (@pair _5154 _5153 x y))) (@pair _5154 _5153 p1 p2))).
