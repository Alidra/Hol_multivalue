Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARITH_EXP_term_abbrevs.
Require Import thm515916_spec.
Require Import thm516204_spec.
Lemma lem516205 : term0.
Proof. exact (EQ_MP (@lem515916) (@lem516204)). Qed.
