Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1098924_term_abbrevs.
Lemma lem1098924 {_25251 : Type'} (h : _25251) (t : list _25251) : (term0 _25251 h t) = ((term1 _25251 h t) = (term2 _25251 h t)).
Proof. exact (eq_refl (term0 _25251 h t)). Qed.
