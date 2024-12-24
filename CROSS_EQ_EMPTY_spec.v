Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4326997 : forall {_103840 _103844 : Type'}, forall s : _103840 -> Prop, forall t : _103844 -> Prop, ((@CROSS _103844 _103840 s t) = (@EMPTY (prod _103840 _103844))) = ((s = (@EMPTY _103840)) \/ (t = (@EMPTY _103844))).
