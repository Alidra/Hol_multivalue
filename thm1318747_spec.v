Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1318747 : (forall x : nadd, forall y : nadd, (nadd_eq x y) = ((mk_hreal (nadd_eq x)) = (mk_hreal (nadd_eq y)))) /\ ((forall P : hreal -> Prop, (forall x : nadd, P (mk_hreal (nadd_eq x))) = (forall x : hreal, P x)) /\ ((forall P : hreal -> Prop, (exists x : nadd, P (mk_hreal (nadd_eq x))) = (exists x : hreal, P x)) /\ (forall x : hreal, (mk_hreal (nadd_eq (@ε nadd (dest_hreal x)))) = x))).
