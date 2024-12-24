Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_INV_1_term_abbrevs.
Require Import thm1592014_spec.
Require Import thm1592030_spec.
Lemma lem1592031 : term0 = term1.
Proof. exact (@lem1592014 (@lem1592030)). Qed.
