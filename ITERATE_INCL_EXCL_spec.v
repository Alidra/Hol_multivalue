Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5778669 : forall {_120960 _120978 : Type'}, forall op : _120978 -> _120978 -> _120978, (@monoidal _120978 op) -> forall s : _120960 -> Prop, forall t : _120960 -> Prop, forall f : _120960 -> _120978, ((@FINITE _120960 s) /\ (@FINITE _120960 t)) -> (op (@iterate _120978 _120960 op s f) (@iterate _120978 _120960 op t f)) = (op (@iterate _120978 _120960 op (@UNION _120960 s t) f) (@iterate _120978 _120960 op (@INTER _120960 s t) f)).
