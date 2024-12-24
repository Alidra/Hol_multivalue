Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7123532 : forall {_133036 : Type'}, forall f : _133036 -> real, forall x : _133036, (@sum _133036 (@INSERT _133036 x (@EMPTY _133036)) f) = (f x).
