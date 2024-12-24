Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem52761 : forall {_5264 _5271 _5272 : Type'}, (forall f : (prod _5272 _5271) -> _5264, (@GABS ((prod _5272 _5271) -> _5264) (fun f' : (prod _5272 _5271) -> _5264 => forall x : _5272, forall y : _5271, @GEQ _5264 (f' (@pair _5272 _5271 x y)) (f (@pair _5272 _5271 x y)))) = f) = (forall f : (prod _5272 _5271) -> _5264, (@GABS ((prod _5272 _5271) -> _5264) (fun f' : (prod _5272 _5271) -> _5264 => forall x : _5272, forall y : _5271, @GEQ _5264 (f' (@pair _5272 _5271 x y)) (f (@pair _5272 _5271 x y)))) = f).
