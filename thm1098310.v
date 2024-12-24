Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1098310_term_abbrevs.
Lemma lem1098310 {A : Type'} : (@LAST A) = (term0 A).
Proof. exact (@LAST_def A). Qed.
