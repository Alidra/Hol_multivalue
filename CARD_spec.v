Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3840377 : forall {_99571 : Type'}, forall s : _99571 -> Prop, (@CARD _99571 s) = (@ITSET nat _99571 (fun x : _99571 => fun n : nat => S n) s (NUMERAL 0)).
