Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_DCHAIN_term_abbrevs.
Require Import thm310219_spec.
Require Import thm316636_spec.
Lemma lem316637 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term0 A lt2).
Proof. exact (EQ_MP (@lem310219 A lt2) (@lem316636 A lt2)). Qed.
