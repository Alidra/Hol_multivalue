Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1164506 : forall {_27428 _27429 : Type'}, forall P : _27429 -> _27428 -> Prop, forall Q : _27429 -> _27428 -> Prop, forall l : list _27429, forall m : list _27428, ((@ALL2 _27429 _27428 P l m) /\ (@ALL2 _27429 _27428 Q l m)) = (@ALL2 _27429 _27428 (fun x : _27429 => fun y : _27428 => (P x y) /\ (Q x y)) l m).
