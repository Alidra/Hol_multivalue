Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1110670_term_abbrevs.
Require Import thm1110669_spec.
Lemma lem1110670 {A : Type'} : term0 A.
Proof. exact (proj2 (@lem1110669 A)). Qed.
