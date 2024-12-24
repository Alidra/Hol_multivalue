Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5772504 : forall {_120745 _120749 : Type'}, forall op : _120749 -> _120749 -> _120749, (@monoidal _120749 op) -> forall f : _120745 -> _120749, forall s : _120745 -> Prop, forall t : _120745 -> Prop, ((@FINITE _120745 s) /\ (@SUBSET _120745 t s)) -> (op (@iterate _120749 _120745 op (@DIFF _120745 s t) f) (@iterate _120749 _120745 op t f)) = (@iterate _120749 _120745 op s f).
