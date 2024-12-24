Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1164040 : forall {_27380 _27381 _27382 _27383 : Type'} (P : _27381 -> _27380 -> Prop) (f : _27382 -> _27381) (g : _27383 -> _27380), forall l : list _27382, forall m : list _27383, (@ALL2 _27381 _27380 P (@List.map _27382 _27381 f l) (@List.map _27383 _27380 g m)) = (@ALL2 _27382 _27383 (fun x : _27382 => fun y : _27383 => P (f x) (g y)) l m).
