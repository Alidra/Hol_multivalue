Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem512702 : forall {_17389 : Type'} (P : _17389 -> Prop) (e : _17389) (Q : Prop), (~ ((forall m : _17389, (P m) -> (m = e) -> Q) = ((P e) -> Q))) -> False.
