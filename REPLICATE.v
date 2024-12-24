Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REPLICATE_term_abbrevs.
Require Import thm1099513_spec.
Require Import thm1099517_spec.
Require Import thm1099518_spec.
Lemma lem1099519 {_25272 : Type'} (n : nat) (x : _25272) : (term0 _25272 n x) = (term1 _25272 n x).
Proof. exact (EQ_MP (@lem1099518 _25272 n x) (@lem1099517 _25272 n x)). Qed.
Lemma lem1099520 {_25272 : Type'} (n : nat) (x : _25272) : term2 _25272 n x.
Proof. exact (conj (@lem1099513 _25272 x) (@lem1099519 _25272 n x)). Qed.
