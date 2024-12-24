Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1111458_term_abbrevs.
Require Import thm1111457_spec.
Lemma lem1111458 {A : Type'} : term0 A.
Proof. exact (proj2 (@lem1111457 A)). Qed.
