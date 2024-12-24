Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1099518_term_abbrevs.
Lemma lem1099518 {_25272 : Type'} (n : nat) (x : _25272) : (term0 _25272 n x) = ((term1 _25272 n x) = (term2 _25272 n x)).
Proof. exact (eq_refl (term0 _25272 n x)). Qed.
