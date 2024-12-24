Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem44160 : forall {_4656 _4660 : Type'}, (@_MATCH _4656 _4660) = (fun e : _4656 => fun r : _4656 -> _4660 -> Prop => @COND _4660 (@ex1 _4660 (r e)) (@ε _4660 (r e)) (@ε _4660 (fun z : _4660 => False))).
