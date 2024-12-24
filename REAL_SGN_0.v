Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SGN_0_term_abbrevs.
Require Import thm1710179_spec.
Require Import thm1710422_spec.
Lemma lem1710423 : term0 = term1.
Proof. exact (EQ_MP (@lem1710179) (@lem1710422)). Qed.
