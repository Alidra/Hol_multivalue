Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4409263 : forall {_106081 _106082 : Type'}, forall s : _106082 -> _106081 -> Prop, (@cartesian_product _106081 _106082 (@EMPTY _106082) s) = (@INSERT (_106082 -> _106081) (fun i : _106082 => @ARB _106081) (@EMPTY (_106082 -> _106081))).
