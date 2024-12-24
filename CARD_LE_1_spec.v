Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4118304 : forall {A : Type'}, forall s : A -> Prop, ((@FINITE A s) /\ (Peano.le (@CARD A s) (NUMERAL (BIT1 0)))) = (exists a : A, @SUBSET A s (@INSERT A a (@EMPTY A))).
