Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FORALL_ONE_THM_term_abbrevs.
Require Import thm16264_spec.
Require Import thm16265_spec.
Lemma lem16266 (P : unit -> Prop) : (term0 P) = (P tt).
Proof. exact (EQ_MP (@lem16265 P) (@lem16264 P)). Qed.
