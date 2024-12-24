Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NOT_CLAUSES_WEAK_term_abbrevs.
Require Import thm1492_spec.
Require Import thm1501_spec.
Require Import thm1502_spec.
Lemma lem1503 : (~ False) = True.
Proof. exact (EQ_MP (@lem1502) (@lem1501)). Qed.
Lemma lem1504 : term0.
Proof. exact (conj (@lem1492) (@lem1503)). Qed.
