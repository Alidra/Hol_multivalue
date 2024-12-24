Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8096071 : forall {_143606 _143608 _143614 : Type'}, forall lt2 : _143606 -> _143606 -> Prop, forall p : (_143606 -> _143608) -> _143614 -> Prop, forall s : _143614 -> _143606, forall t : (_143606 -> _143608) -> _143614 -> _143608, (@superadmissible _143606 _143608 _143614 lt2 p s t) = ((@admissible _143606 _143608 _143606 Prop _143614 lt2 (fun f : _143606 -> _143608 => fun a : _143614 => True) s p) -> @tailadmissible _143606 _143608 _143614 lt2 p s t).
