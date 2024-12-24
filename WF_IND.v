Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import WF_IND_term_abbrevs.
Require Import thm307612_spec.
Require Import thm309905_spec.
Lemma lem309906 {A : Type'} (lt2 : type1402 A) : (@WF A lt2) = (term0 A lt2).
Proof. exact (EQ_MP (@lem307612 A lt2) (@lem309905 A lt2)). Qed.
