Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1094834_term_abbrevs.
Lemma lem1094834 {A : Type'} : (@hd A) = (term0 A).
Proof. exact (@HD_def A). Qed.
