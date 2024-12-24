Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3329633 : forall {_86951 : Type'}, forall s : (_86951 -> Prop) -> Prop, ((@UNIONS _86951 s) = (@EMPTY _86951)) = (forall t : _86951 -> Prop, (@IN (_86951 -> Prop) t s) -> t = (@EMPTY _86951)).
