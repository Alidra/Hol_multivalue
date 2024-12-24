Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3612894 : forall {_92445 : Type'}, forall s : (_92445 -> Prop) -> Prop, (@FINITE (_92445 -> Prop) s) -> (@FINITE _92445 (@UNIONS _92445 s)) = (forall t : _92445 -> Prop, (@IN (_92445 -> Prop) t s) -> @FINITE _92445 t).
