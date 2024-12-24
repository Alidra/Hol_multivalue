Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_REC_EXISTS_term_abbrevs.
Require Import thm358361_spec.
Lemma lem358362 {A B : Type'} (lt2 : type1402 A) : term0 A B lt2.
Proof. exact (fun h0 : @WF A lt2 => @lem358361 A B lt2 h0). Qed.
