Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4437166 : forall {_106515 _106516 : Type'}, forall k : _106515 -> Prop, forall x : _106515 -> _106516, (@cartesian_product _106516 _106515 k (fun i : _106515 => @INSERT _106516 (x i) (@EMPTY _106516))) = (@INSERT (_106515 -> _106516) (@RESTRICTION _106515 _106516 k x) (@EMPTY (_106515 -> _106516))).
