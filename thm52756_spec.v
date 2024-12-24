Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem52756 : forall {_5284 _5296 _5299 _5300 : Type'}, forall f : (prod _5296 (prod _5300 _5299)) -> _5284, (@GABS ((prod _5296 (prod _5300 _5299)) -> _5284) (fun f' : (prod _5296 (prod _5300 _5299)) -> _5284 => forall x : _5296, forall y : _5300, forall z : _5299, @GEQ _5284 (f' (@pair _5296 (prod _5300 _5299) x (@pair _5300 _5299 y z))) (f (@pair _5296 (prod _5300 _5299) x (@pair _5300 _5299 y z))))) = f.
