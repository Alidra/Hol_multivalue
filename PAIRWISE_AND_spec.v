Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4802030 : forall {_110654 : Type'}, forall R : _110654 -> _110654 -> Prop, forall R' : _110654 -> _110654 -> Prop, forall s : _110654 -> Prop, ((@pairwise _110654 R s) /\ (@pairwise _110654 R' s)) = (@pairwise _110654 (fun x : _110654 => fun y : _110654 => (R x y) /\ (R' x y)) s).
