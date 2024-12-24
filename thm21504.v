Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21504_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Lemma lem21502 (a : Prop) : term0 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem21503 (a : Prop) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem21504 (a : Prop) : term1 a.
Proof. exact (EQ_MP (@lem21503 a) (@lem21502 a)). Qed.
