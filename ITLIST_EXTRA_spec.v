Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1129577 : forall {_26663 _26664 : Type'} (f : _26664 -> _26663 -> _26663) (a : _26664) (b : _26663), forall l : list _26664, (@ITLIST _26663 _26664 f (@List.app _26664 l (@cons _26664 a (@nil _26664))) b) = (@ITLIST _26663 _26664 f l (f a b)).
