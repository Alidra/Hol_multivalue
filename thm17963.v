Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm17963_term_abbrevs.
Require Import NOT_EXISTS_THM_spec.
Lemma lem17963 {A : Type'} (P : A -> Prop) : term0 A P.
Proof. exact (@lem10660 A P). Qed.
