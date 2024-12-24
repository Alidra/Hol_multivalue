Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3921542 : forall {_100951 : Type'}, forall a : _100951 -> Prop, forall b : _100951 -> Prop, ((@SUBSET _100951 a b) /\ (~ ((@CARD _100951 a) = (@CARD _100951 b)))) -> @PSUBSET _100951 a b.
