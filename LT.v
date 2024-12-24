Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LT_term_abbrevs.
Require Import thm89994_spec.
Lemma lem89995 : term0.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem89996 : term1.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem89997 : term2.
Proof. exact (conj (@lem89996) (@lem89995)). Qed.
