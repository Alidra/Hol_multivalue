Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6960691 : forall {_127448 : Type'}, forall f : _127448 -> nat, forall x : _127448, (@nsum _127448 (@INSERT _127448 x (@EMPTY _127448)) f) = (f x).
