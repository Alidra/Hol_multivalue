Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3070930_term_abbrevs.
Require Import INT_ABS_POS_spec.
Lemma lem3070928 (x : int) : term0 x.
Proof. exact (@lem2300522 x). Qed.
Lemma lem3070929 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem3070930 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem3070929 x) (@lem3070928 x)). Qed.
