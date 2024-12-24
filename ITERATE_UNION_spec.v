Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5764203 : forall {_120592 _120607 : Type'}, forall op : _120607 -> _120607 -> _120607, (@monoidal _120607 op) -> forall f : _120592 -> _120607, forall s : _120592 -> Prop, forall t : _120592 -> Prop, ((@FINITE _120592 s) /\ ((@FINITE _120592 t) /\ (@DISJOINT _120592 s t))) -> (@iterate _120607 _120592 op (@UNION _120592 s t) f) = (op (@iterate _120607 _120592 op s f) (@iterate _120607 _120592 op t f)).
