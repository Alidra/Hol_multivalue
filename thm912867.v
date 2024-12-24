Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm912867_term_abbrevs.
Require Import thm715609_spec.
Require Import thm715612_spec.
Lemma lem912867 : term0 = term1.
Proof. exact (TRANS (@lem715609) (@lem715612)). Qed.
