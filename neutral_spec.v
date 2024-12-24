Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5711574 : forall {_119565 : Type'}, forall op : _119565 -> _119565 -> _119565, (@neutral _119565 op) = (@ε _119565 (fun x : _119565 => forall y : _119565, ((op x y) = y) /\ ((op y x) = y))).
