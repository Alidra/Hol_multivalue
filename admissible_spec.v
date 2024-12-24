Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8093231 : forall {_143449 _143452 _143456 _143457 _143462 : Type'}, forall p : (_143456 -> _143452) -> _143462 -> Prop, forall lt2 : _143456 -> _143449 -> Prop, forall s : _143462 -> _143449, forall t : (_143456 -> _143452) -> _143462 -> _143457, (@admissible _143449 _143452 _143456 _143457 _143462 lt2 p s t) = (forall f : _143456 -> _143452, forall g : _143456 -> _143452, forall a : _143462, ((p f a) /\ ((p g a) /\ (forall z : _143456, (lt2 z (s a)) -> (f z) = (g z)))) -> (t f a) = (t g a)).
