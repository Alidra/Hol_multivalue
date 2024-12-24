Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1068509_term_abbrevs.
Lemma lem1068509 {A B : Type'} : (@OUTL A B) = (term0 A B).
Proof. exact (@OUTL_def A B). Qed.
