Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4813739 : forall {_110796 _110799 : Type'} (s : _110799 -> Prop), forall r : _110796 -> _110796 -> Prop, forall f : _110799 -> _110796, (@pairwise _110796 r (@IMAGE _110799 _110796 f s)) = (@pairwise _110799 (fun x : _110799 => fun y : _110799 => (~ ((f x) = (f y))) -> r (f x) (f y)) s).
