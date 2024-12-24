Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem53824 : forall {_5456 _5462 _5463 : Type'}, forall P : ((prod _5463 _5462) -> _5456) -> Prop, (forall f : (prod _5463 _5462) -> _5456, P f) = (forall f : _5463 -> _5462 -> _5456, P (@GABS ((prod _5463 _5462) -> _5456) (fun f' : (prod _5463 _5462) -> _5456 => forall a : _5463, forall b : _5462, @GEQ _5456 (f' (@pair _5463 _5462 a b)) (f a b)))).
