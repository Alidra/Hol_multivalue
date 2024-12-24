Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm912803_term_abbrevs.
Require Import thm712018_spec.
Require Import thm712026_spec.
Lemma lem912803 : term0 = term1.
Proof. exact (TRANS (@lem712018) (@lem712026)). Qed.
