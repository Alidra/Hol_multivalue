Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5128794 : forall {_115054 _115057 : Type'}, forall s : _115054 -> Prop, forall t : _115057 -> Prop, (@le_c _115057 _115054 s t) = (exists g : _115057 -> _115054, forall x : _115054, (@IN _115054 x s) -> exists y : _115057, (@IN _115057 y t) /\ ((g y) = x)).
