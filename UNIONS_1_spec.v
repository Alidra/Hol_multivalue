Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3322872 : forall {_86807 : Type'} (s : _86807 -> Prop), (@UNIONS _86807 (@INSERT (_86807 -> Prop) s (@EMPTY (_86807 -> Prop)))) = s.
