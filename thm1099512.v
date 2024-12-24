Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1099512_term_abbrevs.
Lemma lem1099512 {_25272 : Type'} (x : _25272) : (term0 _25272 x) = ((term1 _25272 x) = (@nil _25272)).
Proof. exact (eq_refl (term0 _25272 x)). Qed.
