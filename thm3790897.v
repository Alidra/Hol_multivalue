Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm3790897_term_abbrevs.
Lemma lem3790897 {A B : Type'} : (@FINREC A B) = (term0 A B).
Proof. exact (@FINREC_def A B). Qed.
