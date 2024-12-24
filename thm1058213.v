Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1058213_term_abbrevs.
Lemma lem1058213 {A : Type'} : (@ZBOT A) = (term0 A).
Proof. exact (@ZBOT_def A). Qed.
