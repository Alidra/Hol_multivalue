Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem8100074 : forall {_143669 _143670 _143671 _143672 _143673 : Type'} (lt2 : _143670 -> _143669 -> Prop), forall p : (_143670 -> _143671) -> _143672 -> Prop, forall s : _143672 -> _143669, forall c : _143672 -> _143673, @admissible _143669 _143671 _143670 _143673 _143672 lt2 p s (fun f : _143670 -> _143671 => c).
