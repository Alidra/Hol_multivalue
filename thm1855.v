Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1855_term_abbrevs.
Require Import EQ_CLAUSES_spec.
Lemma lem1853 (t : Prop) : term0 t.
Proof. exact (@lem1445 t). Qed.
Lemma lem1854 (t : Prop) : (term0 t) = (term1 t).
Proof. exact (eq_refl (term0 t)). Qed.
Lemma lem1855 (t : Prop) : term1 t.
Proof. exact (EQ_MP (@lem1854 t) (@lem1853 t)). Qed.
