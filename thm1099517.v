Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1099517_term_abbrevs.
Require Import thm1099509_spec.
Lemma lem1099514 {_25272 : Type'} (n : nat) : term0 _25272 n.
Proof. exact (@lem1099509 _25272 n). Qed.
Lemma lem1099515 {_25272 : Type'} (n : nat) : (term0 _25272 n) = (term1 _25272 n).
Proof. exact (eq_refl (term0 _25272 n)). Qed.
Lemma lem1099516 {_25272 : Type'} (n : nat) : term1 _25272 n.
Proof. exact (EQ_MP (@lem1099515 _25272 n) (@lem1099514 _25272 n)). Qed.
Lemma lem1099517 {_25272 : Type'} (n : nat) (x : _25272) : term2 _25272 n x.
Proof. exact (@lem1099516 _25272 n x). Qed.
