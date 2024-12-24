Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DISJ_ACI_term_abbrevs.
Require Import thm737_spec.
Require Import thm766_spec.
Require Import thm825_spec.
Lemma lem826 (r : Prop) (p : Prop) (q : Prop) : term0 r p q.
Proof. exact (conj (@lem766 p q r) (@lem825 r p q)). Qed.
Lemma lem827 (r : Prop) (p : Prop) (q : Prop) : term1 r p q.
Proof. exact (conj (@lem737 q p) (@lem826 r p q)). Qed.
