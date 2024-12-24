Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4325699 : forall {_103797 _103799 : Type'}, forall s : _103797 -> Prop, forall t : _103799 -> Prop, ((@FINITE _103797 s) /\ (@FINITE _103799 t)) -> (@CARD (prod _103797 _103799) (@CROSS _103799 _103797 s t)) = (Nat.mul (@CARD _103797 s) (@CARD _103799 t)).
