Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_REC_term_abbrevs.
Require Import thm339314_spec.
Lemma lem339315 {A B : Type'} (lt2 : type1402 A) : term0 A B lt2.
Proof. exact (fun h0 : @WF A lt2 => @lem339314 A B lt2 h0). Qed.
