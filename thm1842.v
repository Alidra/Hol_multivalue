Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1842_term_abbrevs.
Require Import AND_CLAUSES_spec.
Lemma lem1840 (t : Prop) : term0 t.
Proof. exact (@lem1567 t). Qed.
Lemma lem1841 (t : Prop) : (term0 t) = (term1 t).
Proof. exact (eq_refl (term0 t)). Qed.
Lemma lem1842 (t : Prop) : term1 t.
Proof. exact (EQ_MP (@lem1841 t) (@lem1840 t)). Qed.
