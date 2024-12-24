Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1095357_term_abbrevs.
Lemma lem1095357 {A : Type'} : (@tl A) = (term0 A).
Proof. exact (@TL_def A). Qed.
