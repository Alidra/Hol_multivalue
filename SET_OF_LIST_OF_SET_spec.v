Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4787453 : forall {_110305 : Type'}, forall s : _110305 -> Prop, (@FINITE _110305 s) -> (@set_of_list _110305 (@list_of_set _110305 s)) = s.
