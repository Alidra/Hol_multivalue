Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem53650 : forall {_5431 _5437 _5438 : Type'}, forall P : ((prod _5438 _5437) -> _5431) -> Prop, (exists f : (prod _5438 _5437) -> _5431, P f) = (exists f : _5438 -> _5437 -> _5431, P (@GABS ((prod _5438 _5437) -> _5431) (fun f' : (prod _5438 _5437) -> _5431 => forall a : _5438, forall b : _5437, @GEQ _5431 (f' (@pair _5438 _5437 a b)) (f a b)))).
