Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5124415 : forall {_115006 _115007 : Type'}, forall t : _115006 -> Prop, forall s : _115007 -> Prop, (@ge_c _115006 _115007 s t) = (@le_c _115007 _115006 t s).
