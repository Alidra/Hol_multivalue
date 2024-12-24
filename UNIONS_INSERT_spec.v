Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3325375 : forall {_86841 : Type'} (s : _86841 -> Prop) (u : (_86841 -> Prop) -> Prop), (@UNIONS _86841 (@INSERT (_86841 -> Prop) s u)) = (@UNION _86841 s (@UNIONS _86841 u)).
