Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1070110_term_abbrevs.
Lemma lem1070110 {A : Type'} : (@Some A) = (term0 A).
Proof. exact (@SOME_def A). Qed.
