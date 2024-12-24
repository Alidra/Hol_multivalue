Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_REC_INVARIANT_term_abbrevs.
Require Import thm322939_spec.
Require Import thm339112_spec.
Lemma lem339113 {A B : Type'} (lt2 : type1402 A) : term0 A B lt2.
Proof. exact (EQ_MP (@lem322939 A B lt2) (@lem339112 A B lt2)). Qed.
