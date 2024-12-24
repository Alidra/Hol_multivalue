Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1184479 : forall {_27538 _27539 _27540 _27541 : Type'} (f : _27540 -> _27539) (g : _27541 -> _27538), forall P : _27539 -> _27538 -> Prop, forall l : list _27540, forall m : list _27541, (@ALLPAIRS _27538 _27539 P (@List.map _27540 _27539 f l) (@List.map _27541 _27538 g m)) = (@ALLPAIRS _27541 _27540 (fun x : _27540 => fun y : _27541 => P (f x) (g y)) l m).
