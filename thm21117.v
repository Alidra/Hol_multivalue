Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm21117_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Lemma lem21115 (p : Prop) : term0 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem21116 (p : Prop) : (term0 p) = (term1 p).
Proof. exact (eq_refl (term0 p)). Qed.
Lemma lem21117 (p : Prop) : term1 p.
Proof. exact (EQ_MP (@lem21116 p) (@lem21115 p)). Qed.
