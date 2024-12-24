Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_THM_term_abbrevs.
Require Import thm9261_spec.
Require Import thm9306_spec.
Lemma lem9307 {A : Type'} : (@ex A) = (term0 A).
Proof. exact (@lem9261 A (@lem9306 A)). Qed.
