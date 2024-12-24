Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5125613 : forall {_115015 _115016 : Type'}, forall t : _115015 -> Prop, forall s : _115016 -> Prop, (@gt_c _115015 _115016 s t) = (@lt_c _115015 _115016 t s).
