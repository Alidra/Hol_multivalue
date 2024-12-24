Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm824_term_abbrevs.
Require Import thm806_spec.
Require Import thm823_spec.
Lemma lem824 (p : Prop) (q : Prop) : term0 p q.
Proof. exact (conj (@lem806 p) (@lem823 p q)). Qed.
