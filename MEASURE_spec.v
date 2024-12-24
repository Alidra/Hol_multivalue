Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem365417 : forall {_16406 : Type'}, forall m : _16406 -> nat, (@MEASURE _16406 m) = (fun x : _16406 => fun y : _16406 => Peano.lt (m x) (m y)).
