Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm4785470_term_abbrevs.
Require Import thm4785465_spec.
Lemma lem4785467 {A : Type'} (h : A) : term0 A h.
Proof. exact (@lem4785465 A h). Qed.
Lemma lem4785468 {A : Type'} (h : A) : (term0 A h) = (term1 A h).
Proof. exact (eq_refl (term0 A h)). Qed.
Lemma lem4785469 {A : Type'} (h : A) : term1 A h.
Proof. exact (EQ_MP (@lem4785468 A h) (@lem4785467 A h)). Qed.
Lemma lem4785470 {A : Type'} (h : A) (t : list A) : term2 A h t.
Proof. exact (@lem4785469 A h t). Qed.
