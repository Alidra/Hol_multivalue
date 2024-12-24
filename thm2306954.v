Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2306954_term_abbrevs.
Require Import thm2306921_spec.
Require Import thm2306953_spec.
Lemma lem2306954 : term0.
Proof. exact (conj (@lem2306953) (@lem2306921)). Qed.
