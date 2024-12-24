Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm163267_term_abbrevs.
Require Import thm89994_spec.
Lemma lem163267 : term0.
Proof. exact (proj1 (@lem89994)). Qed.
