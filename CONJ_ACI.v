Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CONJ_ACI_term_abbrevs.
Require Import thm556_spec.
Require Import thm587_spec.
Require Import thm647_spec.
Lemma lem648 (r : Prop) (p : Prop) (q : Prop) : term0 r p q.
Proof. exact (conj (@lem587 p q r) (@lem647 r p q)). Qed.
Lemma lem649 (r : Prop) (p : Prop) (q : Prop) : term1 r p q.
Proof. exact (conj (@lem556 q p) (@lem648 r p q)). Qed.
