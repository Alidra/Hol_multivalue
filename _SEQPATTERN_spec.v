Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem44157 : forall {_4611 _4614 : Type'}, (@_SEQPATTERN _4611 _4614) = (fun r : _4614 -> _4611 -> Prop => fun s : _4614 -> _4611 -> Prop => fun x : _4614 => @COND (_4611 -> Prop) (exists y : _4611, r x y) (r x) (s x)).
