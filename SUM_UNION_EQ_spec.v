Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7153073 : forall {_133751 : Type'} (f : _133751 -> real), forall s : _133751 -> Prop, forall t : _133751 -> Prop, forall u : _133751 -> Prop, ((@FINITE _133751 u) /\ (((@INTER _133751 s t) = (@EMPTY _133751)) /\ ((@UNION _133751 s t) = u))) -> (real_add (@sum _133751 s f) (@sum _133751 t f)) = (@sum _133751 u f).
