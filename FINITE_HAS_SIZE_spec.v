Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3884233 : forall {_100437 : Type'}, forall s : _100437 -> Prop, (@FINITE _100437 s) = (@HAS_SIZE _100437 s (@CARD _100437 s)).
