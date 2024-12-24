Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1129521 : forall {_26617 _26627 : Type'}, forall f : _26627 -> _26617 -> _26617, forall a : _26617, forall l1 : list _26627, forall l2 : list _26627, (@ITLIST _26617 _26627 f (@List.app _26627 l1 l2) a) = (@ITLIST _26617 _26627 f l1 (@ITLIST _26617 _26627 f l2 a)).
