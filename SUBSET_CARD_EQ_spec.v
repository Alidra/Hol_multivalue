Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3907200 : forall {_100810 : Type'}, forall s : _100810 -> Prop, forall t : _100810 -> Prop, ((@FINITE _100810 t) /\ (@SUBSET _100810 s t)) -> ((@CARD _100810 s) = (@CARD _100810 t)) = (s = t).
