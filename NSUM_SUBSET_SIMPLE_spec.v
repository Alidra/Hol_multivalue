Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7010399 : forall {_128971 : Type'}, forall u : _128971 -> Prop, forall v : _128971 -> Prop, forall f : _128971 -> nat, ((@FINITE _128971 v) /\ (@SUBSET _128971 u v)) -> Peano.le (@nsum _128971 u f) (@nsum _128971 v f).
