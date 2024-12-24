Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARITH_LE_term_abbrevs.
Require Import thm517422_spec.
Require Import thm519779_spec.
Lemma lem519780 : term0.
Proof. exact (EQ_MP (@lem517422) (@lem519779)). Qed.
