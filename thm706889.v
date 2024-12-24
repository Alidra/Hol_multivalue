Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm706889_term_abbrevs.
Require Import thm528257_spec.
Require Import thm528273_spec.
Lemma lem706889 : term0 = term1.
Proof. exact (TRANS (@lem528257) (@lem528273)). Qed.
