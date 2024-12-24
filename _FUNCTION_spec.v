Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem44161 : forall {_4678 _4682 : Type'}, (@_FUNCTION _4678 _4682) = (fun r : _4678 -> _4682 -> Prop => fun x : _4678 => @COND _4682 (@ex1 _4682 (r x)) (@ε _4682 (r x)) (@ε _4682 (fun z : _4682 => False))).
