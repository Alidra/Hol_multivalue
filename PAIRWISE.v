Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PAIRWISE_term_abbrevs.
Require Import thm1110674_spec.
Require Import thm1110681_spec.
Require Import thm1110682_spec.
Lemma lem1110683 {A : Type'} (h : A) (r : type1402 A) (t : list A) : (term0 A r h t) = (term1 A h r t).
Proof. exact (EQ_MP (@lem1110682 A h r t) (@lem1110681 A h r t)). Qed.
Lemma lem1110684 {A : Type'} (h : A) (r : type1402 A) (t : list A) : term2 A h r t.
Proof. exact (conj (@lem1110674 A r) (@lem1110683 A h r t)). Qed.
