Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_NEG_0_term_abbrevs.
Require Import REAL_NEG_0_spec.
Require Import thm2306330_spec.
Lemma lem2306331 : term0 = term1.
Proof. exact (EQ_MP (@lem2306330) (@lem1362041)). Qed.
