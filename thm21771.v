Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21771_term_abbrevs.
Require Import IMP_CLAUSES_spec.
Lemma lem21769 (t : Prop) : term0 t.
Proof. exact (@lem1763 t). Qed.
Lemma lem21770 (t : Prop) : (term0 t) = (term1 t).
Proof. exact (eq_refl (term0 t)). Qed.
Lemma lem21771 (t : Prop) : term1 t.
Proof. exact (EQ_MP (@lem21770 t) (@lem21769 t)). Qed.
