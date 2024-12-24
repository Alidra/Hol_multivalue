Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1820_term_abbrevs.
Require Import IMP_CLAUSES_spec.
Lemma lem1818 (t : Prop) : term0 t.
Proof. exact (@lem1763 t). Qed.
Lemma lem1819 (t : Prop) : (term0 t) = (term1 t).
Proof. exact (eq_refl (term0 t)). Qed.
Lemma lem1820 (t : Prop) : term1 t.
Proof. exact (EQ_MP (@lem1819 t) (@lem1818 t)). Qed.
