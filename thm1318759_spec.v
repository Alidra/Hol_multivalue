Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1318759 : forall (P : hreal -> Prop), (fun P' : hreal -> Prop => (forall x : nadd, P' (mk_hreal (nadd_eq x))) = (forall x : hreal, P' x)) P.
