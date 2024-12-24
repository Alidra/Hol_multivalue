Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PRE_term_abbrevs.
Require Import thm76885_spec.
Lemma lem76886 : term0.
Proof. exact (proj2 (@lem76885)). Qed.
Lemma lem76887 : term1 = (NUMERAL 0).
Proof. exact (proj1 (@lem76885)). Qed.
Lemma lem76888 : term2.
Proof. exact (conj (@lem76887) (@lem76886)). Qed.
