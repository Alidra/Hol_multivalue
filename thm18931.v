Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm18931_term_abbrevs.
Require Import EXISTS_SIMP_spec.
Lemma lem18931 {A : Type'} (t : Prop) : term0 A t.
Proof. exact (@lem1121 A t). Qed.
