Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1177679 : forall {_27459 _27460 : Type'}, forall P : _27460 -> _27459 -> Prop, forall l : list _27460, forall m : list _27459, (@ALLPAIRS _27459 _27460 P l m) = (@ALLPAIRS _27460 _27459 (fun x : _27459 => fun y : _27460 => P y x) m l).
