Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4798413 : forall {_110613 : Type'}, forall r : _110613 -> _110613 -> Prop, forall s : _110613 -> Prop, forall t : _110613 -> Prop, ((@pairwise _110613 r s) /\ (@SUBSET _110613 t s)) -> @pairwise _110613 r t.
