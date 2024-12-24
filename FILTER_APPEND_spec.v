Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1147887 : forall {_27012 : Type'}, forall P : _27012 -> Prop, forall l1 : list _27012, forall l2 : list _27012, (@FILTER _27012 P (@List.app _27012 l1 l2)) = (@List.app _27012 (@FILTER _27012 P l1) (@FILTER _27012 P l2)).
