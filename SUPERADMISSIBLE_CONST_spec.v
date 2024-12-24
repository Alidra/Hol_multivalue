Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8239567 : forall {_145219 _145220 _145221 : Type'} (lt2 : _145219 -> _145219 -> Prop), forall p : (_145219 -> _145221) -> _145220 -> Prop, forall s : _145220 -> _145219, forall c : _145220 -> _145221, @superadmissible _145219 _145221 _145220 lt2 p s (fun f : _145219 -> _145221 => c).
