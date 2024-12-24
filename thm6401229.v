Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm6401229_term_abbrevs.
Lemma lem6401229 {A K : Type'} : (@iterato A K) = (term0 A K).
Proof. exact (@iterato_def A K). Qed.
