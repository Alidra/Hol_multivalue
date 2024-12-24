Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1160417 : forall {_27241 : Type'}, forall P : _27241 -> Prop, forall l1 : list _27241, forall l2 : list _27241, (@List.Forall _27241 P (@List.app _27241 l1 l2)) = ((@List.Forall _27241 P l1) /\ (@List.Forall _27241 P l2)).
