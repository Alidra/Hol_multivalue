Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1100844 : forall {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307), ((fun t' : list _25307 => (@List.Forall _25307 P (@cons _25307 h t')) = ((P h) /\ (@List.Forall _25307 P t'))) t) = ((@List.Forall _25307 P (@cons _25307 h t)) = ((P h) /\ (@List.Forall _25307 P t))).