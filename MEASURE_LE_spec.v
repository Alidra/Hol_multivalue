Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem367111 : forall {_16436 : Type'} (a : _16436) (m : _16436 -> nat) (b : _16436), (forall y : _16436, (@MEASURE _16436 m y a) -> @MEASURE _16436 m y b) = (Peano.le (m a) (m b)).
