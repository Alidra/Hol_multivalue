Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4788175 : forall {_110321 : Type'}, forall s : _110321 -> Prop, (@FINITE _110321 s) -> (@List.length _110321 (@list_of_set _110321 s)) = (@CARD _110321 s).
