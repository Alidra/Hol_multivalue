Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3324017 : forall {_86841 : Type'} (s : _86841 -> Prop) (u : (_86841 -> Prop) -> Prop), (forall x : _86841, (@IN _86841 x (@UNIONS _86841 (@INSERT (_86841 -> Prop) s u))) = (@IN _86841 x (@UNION _86841 s (@UNIONS _86841 u)))) = ((@UNIONS _86841 (@INSERT (_86841 -> Prop) s u)) = (@UNION _86841 s (@UNIONS _86841 u))).
