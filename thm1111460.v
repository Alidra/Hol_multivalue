Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1111460_term_abbrevs.
Require Import thm1111457_spec.
Lemma lem1111459 {A : Type'} : term0 A.
Proof. exact (proj1 (@lem1111457 A)). Qed.
Lemma lem1111460 {A : Type'} (s : nat -> A) : term1 A s.
Proof. exact (@lem1111459 A s). Qed.
