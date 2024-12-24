Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21760_term_abbrevs.
Require Import AND_CLAUSES_spec.
Lemma lem21758 (t : Prop) : term0 t.
Proof. exact (@lem1567 t). Qed.
Lemma lem21759 (t : Prop) : (term0 t) = (term1 t).
Proof. exact (eq_refl (term0 t)). Qed.
Lemma lem21760 (t : Prop) : term1 t.
Proof. exact (EQ_MP (@lem21759 t) (@lem21758 t)). Qed.
