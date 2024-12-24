Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1318736 : forall P : hreal -> Prop, ((exists x : hreal, P x) /\ (exists M : hreal, forall x : hreal, (P x) -> hreal_le x M)) -> exists M : hreal, (forall x : hreal, (P x) -> hreal_le x M) /\ (forall M' : hreal, (forall x : hreal, (P x) -> hreal_le x M') -> hreal_le M M').
