Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem52751 : forall {_5310 _5326 _5330 _5333 _5334 : Type'}, forall f : (prod _5326 (prod _5330 (prod _5334 _5333))) -> _5310, (@GABS ((prod _5326 (prod _5330 (prod _5334 _5333))) -> _5310) (fun f' : (prod _5326 (prod _5330 (prod _5334 _5333))) -> _5310 => forall w : _5326, forall x : _5330, forall y : _5334, forall z : _5333, @GEQ _5310 (f' (@pair _5326 (prod _5330 (prod _5334 _5333)) w (@pair _5330 (prod _5334 _5333) x (@pair _5334 _5333 y z)))) (f (@pair _5326 (prod _5330 (prod _5334 _5333)) w (@pair _5330 (prod _5334 _5333) x (@pair _5334 _5333 y z)))))) = f.
