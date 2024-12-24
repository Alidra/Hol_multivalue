Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm912743_term_abbrevs.
Require Import thm709122_spec.
Require Import thm709125_spec.
Lemma lem912743 : term0 = term1.
Proof. exact (TRANS (@lem709122) (@lem709125)). Qed.
