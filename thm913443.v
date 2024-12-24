Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm913443_term_abbrevs.
Require Import thm759283_spec.
Require Import thm759298_spec.
Lemma lem913443 : term0 = term1.
Proof. exact (TRANS (@lem759283) (@lem759298)). Qed.
