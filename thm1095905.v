Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1095905_term_abbrevs.
Lemma lem1095905 {A : Type'} : (@List.app A) = (term0 A).
Proof. exact (@APPEND_def A). Qed.
