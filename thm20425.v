Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm20425_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Lemma lem20423 (b : Prop) : term0 b.
Proof. exact (@lem9851 b). Qed.
Lemma lem20424 (b : Prop) : (term0 b) = (term1 b).
Proof. exact (eq_refl (term0 b)). Qed.
Lemma lem20425 (b : Prop) : term1 b.
Proof. exact (EQ_MP (@lem20424 b) (@lem20423 b)). Qed.