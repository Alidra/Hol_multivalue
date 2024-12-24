Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1058925_term_abbrevs.
Require Import thm1058924_spec.
Lemma lem1058925 {A : Type'} : term0 A.
Proof. exact (proj2 (@lem1058924 A)). Qed.
