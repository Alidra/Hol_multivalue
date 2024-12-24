Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm913059_term_abbrevs.
Require Import thm728149_spec.
Require Import thm728158_spec.
Lemma lem913059 : term0 = term1.
Proof. exact (TRANS (@lem728149) (@lem728158)). Qed.
