Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4794990 : forall {_110540 : Type'}, forall r : _110540 -> _110540 -> Prop, forall x : _110540, (@pairwise _110540 r (@INSERT _110540 x (@EMPTY _110540))) = True.
