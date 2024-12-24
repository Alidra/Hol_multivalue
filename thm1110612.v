Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1110612_term_abbrevs.
Lemma lem1110612 {A : Type'} : (@List.ForallOrdPairs A) = (term0 A).
Proof. exact (@PAIRWISE_def A). Qed.
