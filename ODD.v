Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ODD_term_abbrevs.
Require Import thm124616_spec.
Lemma lem124617 : term0.
Proof. exact (proj2 (@lem124616)). Qed.
Lemma lem124618 : term1 = False.
Proof. exact (proj1 (@lem124616)). Qed.
Lemma lem124619 : term2.
Proof. exact (conj (@lem124618) (@lem124617)). Qed.
