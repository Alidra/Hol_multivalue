Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1103201_term_abbrevs.
Lemma lem1103201 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : (term0 _25376 h x t) = ((term1 _25376 x h t) = (term2 _25376 h x t)).
Proof. exact (eq_refl (term0 _25376 h x t)). Qed.
