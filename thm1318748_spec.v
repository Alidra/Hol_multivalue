Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1318748 : (forall P : hreal -> Prop, (forall x : nadd, P (mk_hreal (nadd_eq x))) = (forall x : hreal, P x)) /\ ((forall P : hreal -> Prop, (exists x : nadd, P (mk_hreal (nadd_eq x))) = (exists x : hreal, P x)) /\ (forall x : hreal, (mk_hreal (nadd_eq (@ε nadd (dest_hreal x)))) = x)).
