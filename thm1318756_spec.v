Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1318756 : forall (P : hreal -> Prop), ((fun P' : hreal -> Prop => (exists x : nadd, P' (mk_hreal (nadd_eq x))) = (exists x : hreal, P' x)) P) = ((exists x : nadd, P (mk_hreal (nadd_eq x))) = (exists x : hreal, P x)).
