Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4325576 : forall {_103774 _103776 : Type'}, forall s : _103774 -> Prop, forall t : _103776 -> Prop, ((@FINITE _103774 s) /\ (@FINITE _103776 t)) -> @FINITE (prod _103774 _103776) (@CROSS _103776 _103774 s t).
