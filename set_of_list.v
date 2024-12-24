Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import set_of_list_term_abbrevs.
Require Import thm4785466_spec.
Require Import thm4785470_spec.
Require Import thm4785471_spec.
Lemma lem4785472 {A : Type'} (h : A) (t : list A) : (term0 A h t) = (term1 A h t).
Proof. exact (EQ_MP (@lem4785471 A h t) (@lem4785470 A h t)). Qed.
Lemma lem4785473 {A : Type'} (h : A) (t : list A) : term2 A h t.
Proof. exact (conj (@lem4785466 A) (@lem4785472 A h t)). Qed.
