Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3631342 : forall {_93152 : Type'}, forall s : _93152 -> Prop, (@INFINITE _93152 s) -> ~ (s = (@EMPTY _93152)).
