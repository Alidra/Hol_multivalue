Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1102440_term_abbrevs.
Lemma lem1102440 {_25350 _25351 : Type'} (h : _25351) (f : type1467 _25350 _25351) (t : list _25351) (b : _25350) : (term0 _25350 _25351 h f t b) = ((term1 _25350 _25351 f h t b) = (term2 _25350 _25351 h f t b)).
Proof. exact (eq_refl (term0 _25350 _25351 h f t b)). Qed.
