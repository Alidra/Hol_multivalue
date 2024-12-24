Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3923328 : forall {_100977 : Type'}, forall a : _100977 -> Prop, forall b : _100977 -> Prop, ((@FINITE _100977 b) /\ (@SUBSET _100977 a b)) -> (@PSUBSET _100977 a b) = (Peano.lt (@CARD _100977 a) (@CARD _100977 b)).
